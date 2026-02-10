"""Z3 encoder for BUSAT problems."""

from __future__ import annotations

import ast
from typing import Any

import z3

from busat.parser import BusatProblem, BusInteraction, MemInteraction


class EncoderError(Exception):
    """Error during encoding of a BUSAT problem to Z3."""


class BusatEncoder:
    """Translates a BusatProblem into Z3 constraints."""

    def __init__(self, problem: BusatProblem) -> None:
        self.problem = problem
        self._z3_vars: dict[str, z3.ArithRef] = {}
        self._match_vars: dict[tuple[int, int], z3.BoolRef] = {}

    def encode(self) -> list[Any]:
        """Encode the full problem as a list of Z3 constraints."""
        self._collect_variables()
        constraints: list[Any] = []
        constraints.extend(self._encode_definitions())
        constraints.extend(self._encode_constraints())
        if self.problem.buses:
            constraints.extend(self._encode_matching_group(self.problem.buses, "m"))
        if self.problem.mems:
            constraints.extend(self._encode_matching_group(self.problem.mems, "mm"))
            constraints.extend(self._encode_mem_self_balancing(self.problem.mems))
        return constraints

    def get_z3_vars(self) -> dict[str, z3.ArithRef]:
        """Return the mapping of variable names to Z3 variables (excludes integer literals)."""
        return {name: var for name, var in self._z3_vars.items() if not _is_int(name)}

    def get_match_vars(self) -> dict[tuple[int, int], z3.BoolRef]:
        """Return match variables keyed by (bus_id, bus_id) pairs."""
        return dict(self._match_vars)

    def _collect_variables(self) -> None:
        """Walk all expressions and create Z3 Int variables for every name."""
        names: set[str] = set()
        for bus in self.problem.buses:
            names.add(bus.multiplicity)
            names.update(bus.arguments)
        for mem in self.problem.mems:
            names.add(mem.multiplicity)
            names.update(mem.arguments)
        if self.problem.mems:
            names.add("TS_ENTRY")
        for d in self.problem.definitions:
            names.add(d.variable)
            _collect_names(d.expression_ast, names)
        for c in self.problem.constraints:
            _collect_names(c.expression_ast, names)
        for name in sorted(names):
            if _is_int(name):
                self._z3_vars[name] = z3.IntVal(int(name))
            else:
                self._z3_vars[name] = z3.Int(name)

    def _ast_to_z3(self, node: ast.expr) -> Any:
        """Recursively translate a Python AST node to a Z3 expression."""
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return z3.IntVal(node.value)

        if isinstance(node, ast.Name):
            if node.id not in self._z3_vars:
                raise EncoderError(f"unknown variable: {node.id!r}")
            return self._z3_vars[node.id]

        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -self._ast_to_z3(node.operand)

        if isinstance(node, ast.BinOp):
            left = self._ast_to_z3(node.left)
            right = self._ast_to_z3(node.right)
            op = node.op
            if isinstance(op, ast.Add):
                return left + right
            if isinstance(op, ast.Sub):
                return left - right
            if isinstance(op, ast.Mult):
                return left * right
            if isinstance(op, ast.Mod):
                return left % right
            raise EncoderError(f"unsupported binary operator: {type(op).__name__}")

        if isinstance(node, ast.Compare):
            return self._compare_to_z3(node)

        raise EncoderError(f"unsupported AST node: {type(node).__name__}")

    def _compare_to_z3(self, node: ast.Compare) -> Any:
        """Translate a (possibly chained) comparison to Z3."""
        parts = []
        left = self._ast_to_z3(node.left)
        for op, comparator in zip(node.ops, node.comparators):
            right = self._ast_to_z3(comparator)
            parts.append(self._cmp_op(op, left, right))
            left = right
        if len(parts) == 1:
            return parts[0]
        return z3.And(*parts)

    @staticmethod
    def _cmp_op(op: ast.cmpop, left: Any, right: Any) -> Any:
        if isinstance(op, ast.Eq):
            return left == right
        if isinstance(op, ast.NotEq):
            return left != right
        if isinstance(op, ast.Lt):
            return left < right
        if isinstance(op, ast.LtE):
            return left <= right
        if isinstance(op, ast.Gt):
            return left > right
        if isinstance(op, ast.GtE):
            return left >= right
        raise EncoderError(f"unsupported comparison operator: {type(op).__name__}")

    def _encode_definitions(self) -> list[Any]:
        """Encode each definition as var == expr."""
        constraints = []
        for d in self.problem.definitions:
            var = self._z3_vars[d.variable]
            expr = self._ast_to_z3(d.expression_ast)
            constraints.append(var == expr)
        return constraints

    def _encode_constraints(self) -> list[Any]:
        """Encode each constraint expression directly."""
        return [self._ast_to_z3(c.expression_ast) for c in self.problem.constraints]

    def _encode_mem_self_balancing(self, interactions: list[MemInteraction]) -> list[Any]:
        """Encode self-balancing constraints for MEM interactions.

        - Input self-match (mul=-1): timestamp must be < TS_ENTRY
        - Pairwise distinct inputs: different timestamps AND different (as, ptr)
        - Pairwise distinct outputs: different timestamps AND different (as, ptr)
        """
        constraints: list[Any] = []
        ts_entry = self._z3_vars["TS_ENTRY"]

        # Collect self-match vars and field accessors per interaction
        n = len(interactions)
        sm_vars: list[z3.BoolRef] = []
        muls: list[Any] = []
        timestamps: list[Any] = []
        addr_spaces: list[Any] = []
        pointers: list[Any] = []

        bytes_list: list[list[Any]] = []

        for mem in interactions:
            sm_vars.append(self._match_vars[(mem.id, mem.id)])
            muls.append(self._ast_to_z3(ast.Name(id=mem.multiplicity)))
            timestamps.append(self._ast_to_z3(ast.Name(id=mem.timestamp)))
            addr_spaces.append(self._ast_to_z3(ast.Name(id=mem.address_space)))
            pointers.append(self._ast_to_z3(ast.Name(id=mem.pointer)))
            bytes_list.append([
                self._ast_to_z3(ast.Name(id=mem.byte0)),
                self._ast_to_z3(ast.Name(id=mem.byte1)),
                self._ast_to_z3(ast.Name(id=mem.byte2)),
                self._ast_to_z3(ast.Name(id=mem.byte3)),
            ])

        # Per-interaction: input self-match => ts < TS_ENTRY and bytes in [0, 255]
        for i in range(n):
            input_self = z3.And(sm_vars[i], muls[i] == -1)
            constraints.append(z3.Implies(input_self, timestamps[i] < ts_entry))
            for b in bytes_list[i]:
                constraints.append(z3.Implies(input_self, z3.And(b >= 0, b <= 255)))

        # Pairwise constraints for distinct inputs and distinct outputs
        for i in range(n):
            for j in range(i + 1, n):
                # Distinct inputs
                both_input = z3.And(sm_vars[i], muls[i] == -1, sm_vars[j], muls[j] == -1)
                constraints.append(z3.Implies(both_input, timestamps[i] != timestamps[j]))
                constraints.append(
                    z3.Implies(
                        both_input,
                        z3.Not(z3.And(addr_spaces[i] == addr_spaces[j], pointers[i] == pointers[j])),
                    )
                )

                # Distinct outputs
                both_output = z3.And(sm_vars[i], muls[i] == 1, sm_vars[j], muls[j] == 1)
                constraints.append(z3.Implies(both_output, timestamps[i] != timestamps[j]))
                constraints.append(
                    z3.Implies(
                        both_output,
                        z3.Not(z3.And(addr_spaces[i] == addr_spaces[j], pointers[i] == pointers[j])),
                    )
                )

        return constraints

    def _encode_matching_group(
        self, interactions: list[BusInteraction] | list[MemInteraction], prefix: str
    ) -> list[Any]:
        """Encode pairwise matching with pseudo-boolean constraints for a group of interactions."""
        n = len(interactions)
        constraints: list[Any] = []

        # Create match variables for ordered pairs i < j
        match_vars: dict[tuple[int, int], z3.BoolRef] = {}
        for i in range(n):
            for j in range(i + 1, n):
                bi, bj = interactions[i], interactions[j]
                mv = z3.Bool(f"{prefix}_{bi.id}_{bj.id}")
                match_vars[(i, j)] = mv
                self._match_vars[(bi.id, bj.id)] = mv

                # m_i_j => mul_i + mul_j == 0
                mul_i = self._ast_to_z3(ast.Name(id=bi.multiplicity))
                mul_j = self._ast_to_z3(ast.Name(id=bj.multiplicity))
                constraints.append(z3.Implies(mv, mul_i + mul_j == 0))

                # m_i_j => arg_k_i == arg_k_j for all args
                for arg_i, arg_j in zip(bi.arguments, bj.arguments):
                    ai = self._ast_to_z3(ast.Name(id=arg_i))
                    aj = self._ast_to_z3(ast.Name(id=arg_j))
                    constraints.append(z3.Implies(mv, ai == aj))

        # Self-match variables: interaction i balanced by itself
        # Also collect involved match vars per interaction for pseudo-boolean constraints
        involved: dict[int, list[z3.BoolRef]] = {i: [] for i in range(n)}
        for i in range(n):
            bi = interactions[i]
            mv = z3.Bool(f"{prefix}_{bi.id}_{bi.id}")
            self._match_vars[(bi.id, bi.id)] = mv
            involved[i].append(mv)

            # Self-match axiom: MEM allows mul in {-1, 0, 1}; BUS requires mul == 0
            mul_i = self._ast_to_z3(ast.Name(id=bi.multiplicity))
            is_mem = n > 0 and isinstance(interactions[0], MemInteraction)
            if is_mem:
                constraints.append(
                    z3.Implies(mv, z3.Or(mul_i == 0, mul_i == -1, mul_i == 1))
                )
            else:
                constraints.append(z3.Implies(mv, mul_i == 0))

        for (i, j), mv in match_vars.items():
            involved[i].append(mv)
            involved[j].append(mv)

        # Per interaction: exactly one match (AtMost 1 + AtLeast 1)
        for i in range(n):
            constraints.append(z3.AtMost(*involved[i], 1))
            constraints.append(z3.AtLeast(*involved[i], 1))

        return constraints


def _is_int(s: str) -> bool:
    """Check if a string represents an integer literal."""
    try:
        int(s)
        return True
    except ValueError:
        return False


def _collect_names(node: ast.AST, names: set[str]) -> None:
    """Walk an AST and collect all Name nodes."""
    if isinstance(node, ast.Name):
        names.add(node.id)
    for child in ast.iter_child_nodes(node):
        _collect_names(child, names)
