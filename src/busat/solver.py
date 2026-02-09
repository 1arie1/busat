"""Z3 solver integration for BUSAT."""

from typing import Any, Optional
import z3

from busat.parser import parse_file, ParseError
from busat.encoder import BusatEncoder, EncoderError


class BusatSolver:
    """Wrapper around Z3 solver with BUSAT-specific functionality."""

    def __init__(self, timeout: int = 0) -> None:
        """Initialize the solver.

        Args:
            timeout: Solver timeout in milliseconds (0 = no limit)
        """
        self.solver = z3.Solver()
        if timeout > 0:
            self.solver.set("timeout", timeout * 1000)  # Z3 uses milliseconds

    def add_constraint(self, constraint: Any) -> None:
        """Add a constraint to the solver.

        Args:
            constraint: Z3 constraint expression
        """
        self.solver.add(constraint)

    def check_sat(self) -> bool:
        """Check if the current constraints are satisfiable.

        Returns:
            True if satisfiable, False otherwise
        """
        result = self.solver.check()
        return result == z3.sat

    def check(self) -> z3.CheckSatResult:
        """Check satisfiability and return the raw Z3 result."""
        return self.solver.check()

    def get_model(self) -> Optional[z3.ModelRef]:
        """Get a model if the constraints are satisfiable.

        Returns:
            Z3 model if sat, None otherwise
        """
        if self.solver.check() == z3.sat:
            return self.solver.model()
        return None


def encode_from_file(file_path: str) -> str:
    """Parse and encode a BUSAT problem, returning the SMT-LIB2 formula.

    Args:
        file_path: Path to input file

    Returns:
        SMT-LIB2 string of the encoded formula

    Raises:
        ParseError: If parsing fails
        EncoderError: If encoding fails
    """
    problem = parse_file(file_path)
    encoder = BusatEncoder(problem)
    constraints = encoder.encode()
    solver = z3.Solver()
    solver.add(constraints)
    return solver.sexpr()


def solve_from_file(file_path: str, timeout: int = 0) -> dict[str, Any]:
    """Solve a BUSAT problem from a file.

    Args:
        file_path: Path to input file
        timeout: Solver timeout in seconds

    Returns:
        Dictionary with keys: status, model, message
    """
    try:
        problem = parse_file(file_path)
    except ParseError as e:
        return {"status": "error", "model": None, "message": f"Parse error: {e}"}

    try:
        encoder = BusatEncoder(problem)
        constraints = encoder.encode()
    except EncoderError as e:
        return {"status": "error", "model": None, "message": f"Encoding error: {e}"}

    solver = BusatSolver(timeout=timeout)
    for c in constraints:
        solver.add_constraint(c)

    result = solver.check()
    if result == z3.sat:
        z3_model = solver.solver.model()
        z3_vars = encoder.get_z3_vars()
        model = {}
        for name, var in sorted(z3_vars.items()):
            val = z3_model.eval(var, model_completion=True)
            model[name] = val.as_long() if hasattr(val, "as_long") else str(val)
        return {"status": "sat", "model": model, "message": "SAT — satisfying assignment found"}
    elif result == z3.unsat:
        return {"status": "unsat", "model": None, "message": "UNSAT — no satisfying assignment exists"}
    else:
        return {"status": "unknown", "model": None, "message": "UNKNOWN — solver could not decide"}
