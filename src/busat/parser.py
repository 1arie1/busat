"""Parser for BUSAT input files."""

from __future__ import annotations

import ast
import re
from dataclasses import dataclass, field
from pathlib import Path


class ParseError(Exception):
    """Error during parsing of a BUSAT input file."""

    def __init__(self, message: str, line: int | None = None) -> None:
        self.line = line
        if line is not None:
            message = f"line {line}: {message}"
        super().__init__(message)


@dataclass
class BusInteraction:
    id: int
    multiplicity: str
    arguments: list[str]


@dataclass
class Definition:
    variable: str
    expression: str
    expression_ast: ast.expr


@dataclass
class Constraint:
    expression: str
    expression_ast: ast.expr


@dataclass
class BusatProblem:
    buses: list[BusInteraction] = field(default_factory=list)
    definitions: list[Definition] = field(default_factory=list)
    constraints: list[Constraint] = field(default_factory=list)


_SECTION_RE = re.compile(r"^(BUS|DEFS|CONSTRAINTS)\s*$")


def parse_file(path: str | Path) -> BusatProblem:
    """Parse a BUSAT input file."""
    text = Path(path).read_text()
    return parse_text(text)


def parse_text(text: str) -> BusatProblem:
    """Parse BUSAT input from a string."""
    sections = _split_sections(text)
    if "BUS" not in sections:
        raise ParseError("missing BUS section")

    buses = _parse_bus_section(sections["BUS"])
    definitions = _parse_defs_section(sections.get("DEFS", ""))
    constraints = _parse_constraints_section(sections.get("CONSTRAINTS", ""))

    problem = BusatProblem(buses=buses, definitions=definitions, constraints=constraints)
    _validate_problem(problem)
    return problem


def _split_sections(text: str) -> dict[str, str]:
    """Split input text into named sections."""
    sections: dict[str, str] = {}
    current_section: str | None = None
    current_lines: list[str] = []

    for line in text.splitlines():
        m = _SECTION_RE.match(line.strip())
        if m:
            if current_section is not None:
                sections[current_section] = "\n".join(current_lines)
            current_section = m.group(1)
            current_lines = []
        elif current_section is not None:
            current_lines.append(line)

    if current_section is not None:
        sections[current_section] = "\n".join(current_lines)

    return sections


def _parse_bus_section(text: str) -> list[BusInteraction]:
    """Parse BUS section lines of the form 'id: mult, arg1, arg2, ...'."""
    buses: list[BusInteraction] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if ":" not in line:
            raise ParseError(f"expected 'id: mult, arg1, ...' but got: {line!r}", lineno)
        id_part, rest = line.split(":", 1)
        try:
            bus_id = int(id_part.strip())
        except ValueError:
            raise ParseError(f"bus id must be an integer, got: {id_part.strip()!r}", lineno)
        parts = [p.strip() for p in rest.split(",")]
        if len(parts) < 1 or not parts[0]:
            raise ParseError("bus must have at least a multiplicity", lineno)
        multiplicity = parts[0]
        arguments = parts[1:]
        buses.append(BusInteraction(id=bus_id, multiplicity=multiplicity, arguments=arguments))
    return buses


def _parse_defs_section(text: str) -> list[Definition]:
    """Parse DEFS section lines of the form 'var := expr'."""
    defs: list[Definition] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if ":=" not in line:
            raise ParseError(f"expected 'var := expr' but got: {line!r}", lineno)
        var_part, expr_part = line.split(":=", 1)
        variable = var_part.strip()
        expression = expr_part.strip()
        if not variable.isidentifier():
            raise ParseError(f"invalid variable name: {variable!r}", lineno)
        try:
            tree = ast.parse(expression, mode="eval")
        except SyntaxError as e:
            raise ParseError(f"invalid expression: {expression!r}: {e}", lineno)
        defs.append(Definition(variable=variable, expression=expression, expression_ast=tree.body))
    return defs


def _parse_constraints_section(text: str) -> list[Constraint]:
    """Parse CONSTRAINTS section — each non-empty line is a comparison expression."""
    constraints: list[Constraint] = []
    for lineno, line in enumerate(text.splitlines(), start=1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        try:
            tree = ast.parse(line, mode="eval")
        except SyntaxError as e:
            raise ParseError(f"invalid constraint: {line!r}: {e}", lineno)
        constraints.append(Constraint(expression=line, expression_ast=tree.body))
    return constraints


def _validate_problem(problem: BusatProblem) -> None:
    """Validate a parsed problem for consistency."""
    if not problem.buses:
        raise ParseError("at least one bus interaction is required")

    # Unique bus IDs
    seen_ids: set[int] = set()
    for bus in problem.buses:
        if bus.id in seen_ids:
            raise ParseError(f"duplicate bus id: {bus.id}")
        seen_ids.add(bus.id)

    # Consistent arity
    arity = len(problem.buses[0].arguments)
    for bus in problem.buses[1:]:
        if len(bus.arguments) != arity:
            raise ParseError(
                f"bus {bus.id} has {len(bus.arguments)} arguments, "
                f"expected {arity} (from bus {problem.buses[0].id})"
            )

    # Unique definition names
    seen_defs: set[str] = set()
    for d in problem.definitions:
        if d.variable in seen_defs:
            raise ParseError(f"duplicate definition: {d.variable!r}")
        seen_defs.add(d.variable)
