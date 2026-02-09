# BUSAT - Agent Specification

## Overview

BUSAT is a Python CLI tool for solving pairwise satisfiability of bus interaction constraints from OpenVM. It takes a list of bus interactions, variable definitions, and arithmetic constraints, then decides whether the bus interactions can be balanced pairwise (by matching multiplicities), and if so, outputs a satisfying assignment.

## Input Format

The input is a `.bus` text file with three sections:

- **BUS** — bus interactions: `id: multiplicity, arg1, arg2, ...`
- **DEFS** — variable definitions: `var := expr`
- **CONSTRAINTS** — arithmetic constraints

All bus interactions must have the same arity. The first argument is a multiplicity (evaluates to -1, 0, or 1). Integer literals can be used directly in bus definitions.

### Example

```
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
```

## Balancing Rules

Two bus interactions balance when their multiplicities sum to 0 and all corresponding arguments are equal. A bus can self-balance when its multiplicity is 0 (no argument constraints imposed).

A set of bus interactions is balanced if it can be partitioned into balanced pairs.

## SMT Encoding

1. Definitions are encoded as equalities (`var == expr`).
2. Constraints are encoded directly.
3. Bus matching:
   - For each pair `(i, j)`: Boolean `m_i_j` with axioms `m_i_j => mul_i + mul_j == 0` and `m_i_j => arg_k_i == arg_k_j`.
   - For each bus `i`: self-match Boolean `m_i_i` with axiom `m_i_i => mul_i == 0`.
   - Per bus: `AtMost(..., 1)` and `AtLeast(..., 1)` over all its match variables.

## Architecture

```
Input File → Parser → BusatProblem → Encoder → Z3 Constraints → Solver → Result
```

- `parser.py` — parses `.bus` files into `BusatProblem` dataclass using Python `ast` module for expressions
- `encoder.py` — translates `BusatProblem` to Z3 constraints
- `solver.py` — Z3 solver wrapper, `solve_from_file()` pipeline, `encode_from_file()` for SMT output
- `cli.py` — Click CLI with `solve` command

## CLI

```bash
busat solve <input.bus> [--timeout N] [-o output.json] [--show-model] [--encode-only] [-v]
```

Exit codes: 0 = sat, 1 = unsat, 2 = error/unknown.
