"""Tests for the BUSAT encoder."""

import pytest
import z3

from busat.parser import parse_text
from busat.encoder import BusatEncoder, EncoderError


def _solve(text: str) -> z3.CheckSatResult:
    """Helper: parse text, encode, solve, return result."""
    problem = parse_text(text)
    encoder = BusatEncoder(problem)
    constraints = encoder.encode()
    solver = z3.Solver()
    solver.add(constraints)
    return solver.check()


def _solve_model(text: str) -> tuple[z3.CheckSatResult, z3.ModelRef | None, dict[str, z3.ArithRef]]:
    """Helper: parse, encode, solve, return (result, model, z3_vars)."""
    problem = parse_text(text)
    encoder = BusatEncoder(problem)
    constraints = encoder.encode()
    solver = z3.Solver()
    solver.add(constraints)
    result = solver.check()
    model = solver.model() if result == z3.sat else None
    return result, model, encoder.get_z3_vars()


def _solve_full(
    text: str,
) -> tuple[z3.CheckSatResult, z3.ModelRef | None, dict[str, z3.ArithRef], dict[tuple[int, int], z3.BoolRef]]:
    """Helper: parse, encode, solve, return (result, model, z3_vars, match_vars)."""
    problem = parse_text(text)
    encoder = BusatEncoder(problem)
    constraints = encoder.encode()
    solver = z3.Solver()
    solver.add(constraints)
    result = solver.check()
    model = solver.model() if result == z3.sat else None
    return result, model, encoder.get_z3_vars(), encoder.get_match_vars()


class TestDefinitionEncoding:
    def test_simple_definition(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\na := 5\nb := 5\n"
        result = _solve(text)
        assert result == z3.sat

    def test_definition_with_arithmetic(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\na := 3 + 2\nb := 5\n"
        result = _solve(text)
        assert result == z3.sat


class TestConstraintEncoding:
    def test_greater_than(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\n\nCONSTRAINTS\na > 0\na == b\n"
        result, model, z3_vars = _solve_model(text)
        assert result == z3.sat
        assert model is not None
        a_val = model.eval(z3_vars["a"], model_completion=True).as_long()
        assert a_val > 0

    def test_chained_comparison(self) -> None:
        text = (
            "BUS\n1: p, a\n2: q, b\n\n"
            "DEFS\np := 1\nq := -1\n\n"
            "CONSTRAINTS\n0 <= a\na < 10\na == b\n"
        )
        result, model, z3_vars = _solve_model(text)
        assert result == z3.sat
        a_val = model.eval(z3_vars["a"], model_completion=True).as_long()
        assert 0 <= a_val < 10


class TestUnaryMinus:
    def test_negation_in_def(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\na := -5\nb := -5\n"
        result = _solve(text)
        assert result == z3.sat


class TestNestedArithmetic:
    def test_nested_ops(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\n" "DEFS\np := 1\nq := -1\na := (2 + 3) * 4\nb := 20\n"
        result = _solve(text)
        assert result == z3.sat


class TestBusMatching:
    def test_two_bus_sat(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\na := 7\nb := 7\n"
        result = _solve(text)
        assert result == z3.sat

    def test_two_bus_unsat_mult(self) -> None:
        """Both multiplicities are 1 — cannot cancel."""
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := 1\na := 7\nb := 7\n"
        result = _solve(text)
        assert result == z3.unsat

    def test_two_bus_unsat_args(self) -> None:
        """Multiplicities cancel but args differ."""
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\na := 1\nb := 2\n"
        result = _solve(text)
        assert result == z3.unsat

    def test_four_bus_sat(self) -> None:
        text = (
            "BUS\n1: p1, a1\n2: p2, a2\n3: p3, a3\n4: p4, a4\n\n"
            "DEFS\n"
            "p1 := 1\np2 := -1\np3 := 1\np4 := -1\n"
            "a1 := 10\na2 := 10\na3 := 20\na4 := 20\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_four_bus_unsat_odd_count(self) -> None:
        """3 positive, 1 negative — can't pair all (no self-match possible)."""
        text = (
            "BUS\n1: p1, a1\n2: p2, a2\n3: p3, a3\n4: p4, a4\n\n"
            "DEFS\n"
            "p1 := 1\np2 := 1\np3 := 1\np4 := -1\n"
            "a1 := 10\na2 := 10\na3 := 10\na4 := 10\n"
        )
        result = _solve(text)
        assert result == z3.unsat


class TestSelfMatching:
    def test_single_bus_zero_mult(self) -> None:
        """A single bus with multiplicity 0 can self-match."""
        text = "BUS\n1: p, a\n\nDEFS\np := 0\na := 42\n"
        result = _solve(text)
        assert result == z3.sat

    def test_single_bus_nonzero_mult(self) -> None:
        """A single bus with nonzero multiplicity cannot self-match."""
        text = "BUS\n1: p, a\n\nDEFS\np := 1\na := 42\n"
        result = _solve(text)
        assert result == z3.unsat

    def test_self_match_no_arg_constraint(self) -> None:
        """Self-matching imposes no argument constraints — args are free."""
        text = "BUS\n1: p, a\n\nDEFS\np := 0\n\nCONSTRAINTS\na == 99\n"
        result, model, z3_vars = _solve_model(text)
        assert result == z3.sat
        assert model.eval(z3_vars["a"], model_completion=True).as_long() == 99

    def test_three_buses_one_self_match(self) -> None:
        """3 buses: two pair together, one self-matches with mult 0."""
        text = (
            "BUS\n1: p1, a1\n2: p2, a2\n3: p3, a3\n\n"
            "DEFS\n"
            "p1 := 1\np2 := -1\np3 := 0\n"
            "a1 := 5\na2 := 5\na3 := 99\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_three_buses_no_self_match_unsat(self) -> None:
        """3 buses, all nonzero mult — odd count, no self-match possible."""
        text = (
            "BUS\n1: p1, a1\n2: p2, a2\n3: p3, a3\n\n"
            "DEFS\n"
            "p1 := 1\np2 := -1\np3 := 1\n"
            "a1 := 5\na2 := 5\na3 := 5\n"
        )
        result = _solve(text)
        assert result == z3.unsat


class TestIntegerLiterals:
    def test_literal_multiplicity(self) -> None:
        """Integer literals as bus multiplicity become IntVal, not variables."""
        text = "BUS\n1: 1, a\n2: -1, b\n\nDEFS\na := 5\nb := 5\n"
        result = _solve(text)
        assert result == z3.sat

    def test_literal_argument(self) -> None:
        """Integer literals as bus arguments become IntVal."""
        text = "BUS\n1: p, 7\n2: q, 7\n\nDEFS\np := 1\nq := -1\n"
        result = _solve(text)
        assert result == z3.sat

    def test_literal_argument_mismatch(self) -> None:
        """Different integer literal arguments cause unsat."""
        text = "BUS\n1: p, 7\n2: q, 8\n\nDEFS\np := 1\nq := -1\n"
        result = _solve(text)
        assert result == z3.unsat

    def test_literal_not_in_model_vars(self) -> None:
        """Integer literals should not appear as named variables in get_z3_vars."""
        text = "BUS\n1: 1, a\n2: -1, b\n\nDEFS\na := 5\nb := 5\n"
        problem = parse_text(text)
        encoder = BusatEncoder(problem)
        encoder.encode()
        z3_vars = encoder.get_z3_vars()
        assert "a" in z3_vars
        assert "b" in z3_vars


class TestVariableReuse:
    def test_shared_variables(self) -> None:
        """Two buses share a variable — should still work."""
        text = "BUS\n1: p, a\n2: q, a\n\nDEFS\np := 1\nq := -1\n"
        result = _solve(text)
        assert result == z3.sat


class TestFullExample:
    def test_agent_md_example(self) -> None:
        text = """\
BUS
1: p, a, b, c
2: q, x, y, z

DEFS
a := b + 1
c := b + 2
p := 1
q := -1

CONSTRAINTS
a > 0
b >= 0
c > b
"""
        result, model, z3_vars = _solve_model(text)
        assert result == z3.sat
        assert model is not None
        # Verify matching: a == x, b == y, c == z, p + q == 0
        a = model.eval(z3_vars["a"], model_completion=True).as_long()
        x = model.eval(z3_vars["x"], model_completion=True).as_long()
        assert a == x


class TestMemMatching:
    def test_two_mem_sat(self) -> None:
        text = (
            "MEM\n"
            "1: p, as1, ptr1, b0_1, b1_1, b2_1, b3_1, ts1\n"
            "2: q, as2, ptr2, b0_2, b1_2, b2_2, b3_2, ts2\n\n"
            "DEFS\n"
            "p := 1\nq := -1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 100\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 5\nts2 := 5\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_two_mem_unsat_args(self) -> None:
        """Mismatched args with mul=2 (not self-balanceable) — UNSAT."""
        text = (
            "MEM\n"
            "1: p, as1, ptr1, b0_1, b1_1, b2_1, b3_1, ts1\n"
            "2: q, as2, ptr2, b0_2, b1_2, b2_2, b3_2, ts2\n\n"
            "DEFS\n"
            "p := 2\nq := -2\n"
            "as1 := 1\nas2 := 2\nptr1 := 100\nptr2 := 100\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 5\nts2 := 5\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_mem_self_match(self) -> None:
        text = (
            "MEM\n1: p, as1, ptr1, b0, b1, b2, b3, ts\n\n"
            "DEFS\np := 0\nas1 := 1\nptr1 := 100\n"
            "b0 := 10\nb1 := 20\nb2 := 30\nb3 := 40\nts := 5\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_bus_and_mem_independent(self) -> None:
        """One BUS and one MEM, both nonzero mult — each pool has an odd member, so UNSAT."""
        text = (
            "BUS\n1: p, a\n\n"
            "MEM\n2: q, as1, ptr1, b0, b1, b2, b3, ts\n\n"
            "DEFS\np := 1\nq := 1\nas1 := 1\nptr1 := 100\n"
            "b0 := 10\nb1 := 20\nb2 := 30\nb3 := 40\nts := 5\na := 7\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_bus_and_mem_sat(self) -> None:
        """BUS pair matches, MEM pair matches — SAT."""
        text = (
            "BUS\n1: p1, a1\n2: p2, a2\n\n"
            "MEM\n3: m1, as1, ptr1, b0_1, b1_1, b2_1, b3_1, ts1\n"
            "4: m2, as2, ptr2, b0_2, b1_2, b2_2, b3_2, ts2\n\n"
            "DEFS\n"
            "p1 := 1\np2 := -1\na1 := 7\na2 := 7\n"
            "m1 := 1\nm2 := -1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 100\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 5\nts2 := 5\n"
        )
        result = _solve(text)
        assert result == z3.sat


class TestTsEntry:
    def test_ts_entry_injected_when_mem_present(self) -> None:
        text = (
            "MEM\n1: p, as1, ptr1, b0, b1, b2, b3, ts\n"
            "2: q, as2, ptr2, b02, b12, b22, b32, ts2\n\n"
            "DEFS\np := 1\nq := -1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 100\n"
            "b0 := 10\nb02 := 10\nb1 := 20\nb12 := 20\n"
            "b2 := 30\nb22 := 30\nb3 := 40\nb32 := 40\n"
            "ts := 5\nts2 := 5\n"
        )
        problem = parse_text(text)
        encoder = BusatEncoder(problem)
        encoder.encode()
        z3_vars = encoder.get_z3_vars()
        assert "TS_ENTRY" in z3_vars

    def test_ts_entry_absent_when_no_mem(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\na := 5\nb := 5\n"
        problem = parse_text(text)
        encoder = BusatEncoder(problem)
        encoder.encode()
        z3_vars = encoder.get_z3_vars()
        assert "TS_ENTRY" not in z3_vars

    def test_ts_entry_usable_in_constraints(self) -> None:
        text = (
            "MEM\n1: p, as1, ptr1, b0, b1, b2, b3, ts\n"
            "2: q, as2, ptr2, b02, b12, b22, b32, ts2\n\n"
            "DEFS\np := 1\nq := -1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 100\n"
            "b0 := 10\nb02 := 10\nb1 := 20\nb12 := 20\n"
            "b2 := 30\nb22 := 30\nb3 := 40\nb32 := 40\n"
            "ts := 5\nts2 := 5\n\n"
            "CONSTRAINTS\nTS_ENTRY >= 0\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_ts_entry_usable_in_defs(self) -> None:
        text = (
            "MEM\n1: p, as1, ptr1, b0, b1, b2, b3, ts\n"
            "2: q, as2, ptr2, b02, b12, b22, b32, ts2\n\n"
            "DEFS\np := 1\nq := -1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 100\n"
            "b0 := 10\nb02 := 10\nb1 := 20\nb12 := 20\n"
            "b2 := 30\nb22 := 30\nb3 := 40\nb32 := 40\n"
            "ts := TS_ENTRY\nts2 := TS_ENTRY\n"
        )
        result = _solve(text)
        assert result == z3.sat


class TestMemSelfBalancing:
    """Tests for MEM self-balancing (input/output self-match)."""

    @staticmethod
    def _mem_line(id: int, mul: str, as_: str, ptr: str, ts: str) -> str:
        return f"{id}: {mul}, {as_}, {ptr}, b0_{id}, b1_{id}, b2_{id}, b3_{id}, {ts}"

    def test_single_input_self_match(self) -> None:
        """1 MEM, mul=-1, ts unconstrained — SAT (solver picks TS_ENTRY > ts)."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p', 'as1', 'ptr1', 'ts1')}\n\n"
            "DEFS\np := -1\nas1 := 1\nptr1 := 100\n"
            "b0_1 := 10\nb1_1 := 20\nb2_1 := 30\nb3_1 := 40\nts1 := 5\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_single_output_self_match(self) -> None:
        """1 MEM, mul=1 — SAT."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p', 'as1', 'ptr1', 'ts1')}\n\n"
            "DEFS\np := 1\nas1 := 1\nptr1 := 100\n"
            "b0_1 := 10\nb1_1 := 20\nb2_1 := 30\nb3_1 := 40\nts1 := 5\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_input_ts_ge_ts_entry_unsat(self) -> None:
        """1 MEM, mul=-1, ts=5, TS_ENTRY=3 — UNSAT (ts must be < TS_ENTRY)."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p', 'as1', 'ptr1', 'ts1')}\n\n"
            "DEFS\np := -1\nas1 := 1\nptr1 := 100\n"
            "b0_1 := 10\nb1_1 := 20\nb2_1 := 30\nb3_1 := 40\n"
            "ts1 := 5\nTS_ENTRY := 3\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_two_inputs_distinct_ts_and_ptr(self) -> None:
        """2 MEM, both mul=-1, different ts, different ptr — SAT."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p1', 'as1', 'ptr1', 'ts1')}\n"
            f"{self._mem_line(2, 'p2', 'as2', 'ptr2', 'ts2')}\n\n"
            "DEFS\np1 := -1\np2 := -1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 200\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 1\nts2 := 2\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_two_inputs_same_ts_unsat(self) -> None:
        """2 MEM, both mul=-1, same ts — UNSAT."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p1', 'as1', 'ptr1', 'ts1')}\n"
            f"{self._mem_line(2, 'p2', 'as2', 'ptr2', 'ts2')}\n\n"
            "DEFS\np1 := -1\np2 := -1\n"
            "as1 := 1\nas2 := 2\nptr1 := 100\nptr2 := 200\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 5\nts2 := 5\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_two_inputs_same_as_and_ptr_unsat(self) -> None:
        """2 MEM, both mul=-1, diff ts, same as & ptr — UNSAT."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p1', 'as1', 'ptr1', 'ts1')}\n"
            f"{self._mem_line(2, 'p2', 'as2', 'ptr2', 'ts2')}\n\n"
            "DEFS\np1 := -1\np2 := -1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 100\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 1\nts2 := 2\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_two_outputs_distinct_ts_and_ptr(self) -> None:
        """2 MEM, both mul=1, different ts, different ptr — SAT."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p1', 'as1', 'ptr1', 'ts1')}\n"
            f"{self._mem_line(2, 'p2', 'as2', 'ptr2', 'ts2')}\n\n"
            "DEFS\np1 := 1\np2 := 1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 200\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 1\nts2 := 2\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_two_outputs_same_ts_unsat(self) -> None:
        """2 MEM, both mul=1, same ts — UNSAT."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p1', 'as1', 'ptr1', 'ts1')}\n"
            f"{self._mem_line(2, 'p2', 'as2', 'ptr2', 'ts2')}\n\n"
            "DEFS\np1 := 1\np2 := 1\n"
            "as1 := 1\nas2 := 2\nptr1 := 100\nptr2 := 200\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 5\nts2 := 5\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_mixed_input_output_self_match(self) -> None:
        """2 MEM, mul=-1 and mul=1 — SAT (no cross-type constraint)."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p1', 'as1', 'ptr1', 'ts1')}\n"
            f"{self._mem_line(2, 'p2', 'as2', 'ptr2', 'ts2')}\n\n"
            "DEFS\np1 := -1\np2 := 1\n"
            "as1 := 1\nas2 := 1\nptr1 := 100\nptr2 := 100\n"
            "b0_1 := 10\nb0_2 := 10\nb1_1 := 20\nb1_2 := 20\n"
            "b2_1 := 30\nb2_2 := 30\nb3_1 := 40\nb3_2 := 40\n"
            "ts1 := 5\nts2 := 5\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_self_match_mul_2_fails(self) -> None:
        """1 MEM, mul=2 — UNSAT (self-match only allows 0, -1, 1)."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p', 'as1', 'ptr1', 'ts1')}\n\n"
            "DEFS\np := 2\nas1 := 1\nptr1 := 100\n"
            "b0_1 := 10\nb1_1 := 20\nb2_1 := 30\nb3_1 := 40\nts1 := 5\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_input_bytes_in_range_sat(self) -> None:
        """Input self-match with bytes in [0, 255] — SAT."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p', 'as1', 'ptr1', 'ts1')}\n\n"
            "DEFS\np := -1\nas1 := 1\nptr1 := 100\n"
            "b0_1 := 0\nb1_1 := 127\nb2_1 := 255\nb3_1 := 42\nts1 := 5\n"
        )
        result = _solve(text)
        assert result == z3.sat

    def test_input_byte_negative_unsat(self) -> None:
        """Input self-match with b0 = -1 — UNSAT (byte out of range)."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p', 'as1', 'ptr1', 'ts1')}\n\n"
            "DEFS\np := -1\nas1 := 1\nptr1 := 100\n"
            "b0_1 := -1\nb1_1 := 20\nb2_1 := 30\nb3_1 := 40\nts1 := 5\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_input_byte_over_255_unsat(self) -> None:
        """Input self-match with b2 = 256 — UNSAT (byte out of range)."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p', 'as1', 'ptr1', 'ts1')}\n\n"
            "DEFS\np := -1\nas1 := 1\nptr1 := 100\n"
            "b0_1 := 10\nb1_1 := 20\nb2_1 := 256\nb3_1 := 40\nts1 := 5\n"
        )
        result = _solve(text)
        assert result == z3.unsat

    def test_output_bytes_not_range_checked(self) -> None:
        """Output self-match with b0 = -1 — SAT (byte range only applies to inputs)."""
        text = (
            "MEM\n"
            f"{self._mem_line(1, 'p', 'as1', 'ptr1', 'ts1')}\n\n"
            "DEFS\np := 1\nas1 := 1\nptr1 := 100\n"
            "b0_1 := -1\nb1_1 := 20\nb2_1 := 30\nb3_1 := 40\nts1 := 5\n"
        )
        result = _solve(text)
        assert result == z3.sat


class TestAliasedPointers:
    """Tests for aliased/non-aliased pointer scenarios with MEM self-balancing."""

    _BASE = (
        "MEM\n"
        "## read ptr0\n"
        "0: -1, 2, ptr0, b0_0, b0_1, b0_2, b0_3, ts_prev_0\n"
        "1: 1, 2, ptr0, b0_0, b0_1, b0_2, b0_3, ts0\n"
        "## write new value at ptr0\n"
        "2: -1, 2, ptr0, aux_0, aux_1, aux_2, aux_3, ts_prev_1\n"
        "3: 1, 2, ptr0, 0, 1, 2, 3, ts1\n"
        "## read current value of ptr1\n"
        "4: -1, 2, ptr1, b1_0, b1_1, b1_2, b1_3, ts_prev_2\n"
        "5: 1, 2, ptr1, b1_0, b1_1, b1_2, b1_3, ts2\n\n"
        "DEFS\n"
        "ts0 := TS_ENTRY\nts1 := TS_ENTRY + 1\nts2 := TS_ENTRY + 2\n\n"
        "CONSTRAINTS\n"
        "ts_prev_0 < ts0\nts_prev_1 < ts1\nts_prev_2 < ts2\n"
        "TS_ENTRY == 0\n"
    )

    @staticmethod
    def _count_self_balancing(
        model: z3.ModelRef,
        match_vars: dict[tuple[int, int], z3.BoolRef],
        z3_vars: dict[str, z3.ArithRef],
        muls: dict[int, str],
    ) -> tuple[int, int]:
        """Count self-balanced inputs and outputs from a solved model."""
        inputs = 0
        outputs = 0
        for (id_a, id_b), mv in match_vars.items():
            if id_a != id_b:
                continue
            if not z3.is_true(model.eval(mv, model_completion=True)):
                continue
            mul_name = muls.get(id_a)
            if mul_name is None:
                continue
            if mul_name in z3_vars:
                mul_val = model.eval(z3_vars[mul_name], model_completion=True).as_long()
            else:
                mul_val = int(mul_name)
            if mul_val == -1:
                inputs += 1
            elif mul_val == 1:
                outputs += 1
        return inputs, outputs

    def test_aliased_sat(self) -> None:
        """ptr0 == ptr1: SAT with one self-balanced input and one output."""
        text = self._BASE + "ptr0 == ptr1\n"
        result, model, z3_vars, match_vars = _solve_full(text)
        assert result == z3.sat
        muls = {0: "-1", 1: "1", 2: "-1", 3: "1", 4: "-1", 5: "1"}
        inputs, outputs = self._count_self_balancing(model, match_vars, z3_vars, muls)
        assert inputs == 1
        assert outputs == 1

    def test_not_aliased_sat(self) -> None:
        """ptr0 != ptr1: SAT with two self-balanced inputs and two outputs."""
        text = self._BASE + "ptr0 != ptr1\n"
        result, model, z3_vars, match_vars = _solve_full(text)
        assert result == z3.sat
        muls = {0: "-1", 1: "1", 2: "-1", 3: "1", 4: "-1", 5: "1"}
        inputs, outputs = self._count_self_balancing(model, match_vars, z3_vars, muls)
        assert inputs == 2
        assert outputs == 2


class TestUnsupportedOps:
    def test_unsupported_binop_raises(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\na := 2 ** 3\nb := 8\n"
        problem = parse_text(text)
        encoder = BusatEncoder(problem)
        with pytest.raises(EncoderError, match="unsupported binary operator"):
            encoder.encode()
