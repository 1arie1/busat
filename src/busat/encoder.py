"""Z3 encoder for BUSAT problems."""

from __future__ import annotations

import ast
from typing import Any

import z3

from busat.parser import BusatProblem


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
        constraints.extend(self._encode_bus_matching())
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

    def _encode_bus_matching(self) -> list[Any]:
        """Encode pairwise bus matching with pseudo-boolean constraints."""
        buses = self.problem.buses
        n = len(buses)
        constraints: list[Any] = []

        # Create match variables for ordered pairs i < j
        match_vars: dict[tuple[int, int], z3.BoolRef] = {}
        for i in range(n):
            for j in range(i + 1, n):
                bi, bj = buses[i], buses[j]
                mv = z3.Bool(f"m_{bi.id}_{bj.id}")
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

        # Self-match variables: bus i balanced by itself
        # Also collect involved match vars per bus for pseudo-boolean constraints
        involved: dict[int, list[z3.BoolRef]] = {i: [] for i in range(n)}
        for i in range(n):
            bi = buses[i]
            mv = z3.Bool(f"m_{bi.id}_{bi.id}")
            self._match_vars[(bi.id, bi.id)] = mv
            involved[i].append(mv)

            # m_i_i => mul_i == 0
            mul_i = self._ast_to_z3(ast.Name(id=bi.multiplicity))
            constraints.append(z3.Implies(mv, mul_i == 0))

        for (i, j), mv in match_vars.items():
            involved[i].append(mv)
            involved[j].append(mv)

        # Per bus: exactly one match (AtMost 1 + AtLeast 1)
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
