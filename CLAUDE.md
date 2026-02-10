# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
# Install (dev mode with all dependencies)
pip install -e ".[dev]"

# Run all tests
pytest tests/ -v

# Run a single test
pytest tests/test_encoder.py::TestBusMatching::test_two_bus_sat -v

# Format
black src/ tests/

# Type check
mypy src/
```

Black is configured for 100-char line length. MyPy runs in strict mode (`disallow_untyped_defs`).

## Architecture

```
Input File (.bus) → parser.py → BusatProblem → encoder.py → Z3 Constraints → solver.py → Result
```

**parser.py** — Parses `.bus` files (BUS/DEFS/CONSTRAINTS sections) into dataclasses (`BusatProblem`, `BusInteraction`, `Definition`, `Constraint`). Expressions are parsed via Python's `ast` module and stored as `ast.expr` nodes for the encoder to translate.

**encoder.py** — `BusatEncoder` walks the parsed AST nodes and translates them to Z3 expressions (`_ast_to_z3`). Bus matching creates Boolean variables `m_i_j` for each pair and `m_i_i` for self-matching, with implication axioms and `AtMost`/`AtLeast` pseudo-boolean constraints ensuring exactly one match per bus. Names that parse as integers become `z3.IntVal` instead of `z3.Int` variables.

**solver.py** — `BusatSolver` wraps Z3. `solve_from_file()` runs the full pipeline and returns `{"status", "model", "matching", "message"}`. `encode_from_file()` returns the SMT-LIB2 formula without solving.

**cli.py** — Click CLI. The `solve` command supports `--show-model`, `--encode-only`, `--timeout`, `-o`, `-v`. Exit codes: 0=sat, 1=unsat, 2=error.

## Testing

Tests are in 4 files: `test_busat.py` (basic solver), `test_parser.py`, `test_encoder.py`, `test_integration.py` (end-to-end + CLI via `CliRunner`). Fixtures live in `tests/fixtures/*.bus`. Use `parse_text()` for unit tests without filesystem.
