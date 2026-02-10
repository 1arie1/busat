"""Tests for BUSAT."""

import pytest
from busat import __version__
from busat.solver import BusatSolver
import z3


def test_version() -> None:
    """Test that version is defined."""
    assert __version__ == "0.1.0"


def test_solver_initialization() -> None:
    """Test that solver can be initialized."""
    solver = BusatSolver()
    assert solver.solver is not None


def test_simple_sat_check() -> None:
    """Test a simple satisfiability check."""
    solver = BusatSolver()
    x = z3.Int("x")
    solver.add_constraint(x > 0)
    solver.add_constraint(x < 10)
    assert solver.check_sat() is True


def test_simple_unsat_check() -> None:
    """Test a simple unsatisfiability check."""
    solver = BusatSolver()
    x = z3.Int("x")
    solver.add_constraint(x > 10)
    solver.add_constraint(x < 5)
    assert solver.check_sat() is False


def test_get_model() -> None:
    """Test getting a model from satisfiable constraints."""
    solver = BusatSolver()
    x = z3.Int("x")
    solver.add_constraint(x == 42)
    model = solver.get_model()
    assert model is not None
    assert model.eval(x).as_long() == 42
