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
        text = (
            "BUS\n1: p, a\n2: q, b\n\n"
            "DEFS\np := 1\nq := -1\na := (2 + 3) * 4\nb := 20\n"
        )
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
        """3 positive, 1 negative — can't pair all."""
        text = (
            "BUS\n1: p1, a1\n2: p2, a2\n3: p3, a3\n4: p4, a4\n\n"
            "DEFS\n"
            "p1 := 1\np2 := 1\np3 := 1\np4 := -1\n"
            "a1 := 10\na2 := 10\na3 := 10\na4 := 10\n"
        )
        result = _solve(text)
        assert result == z3.unsat


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


class TestUnsupportedOps:
    def test_unsupported_binop_raises(self) -> None:
        text = "BUS\n1: p, a\n2: q, b\n\nDEFS\np := 1\nq := -1\na := 2 ** 3\nb := 8\n"
        problem = parse_text(text)
        encoder = BusatEncoder(problem)
        with pytest.raises(EncoderError, match="unsupported binary operator"):
            encoder.encode()
