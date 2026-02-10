# BUSAT - Agent Specification

## Overview

BUSAT is a Python CLI tool for solving pairwise satisfiability of bus interaction constraints from OpenVM. It takes a list of bus interactions, variable definitions, and arithmetic constraints, then decides whether the bus interactions can be balanced pairwise (by matching multiplicities), and if so, outputs a satisfying assignment.

## Input Format

The input is a `.bus` text file with up to four sections:

- **BUS** — bus interactions: `id: multiplicity, arg1, arg2, ...`
- **MEM** — memory bus interactions: `id: multiplicity, address_space, pointer, b0, b1, b2, b3, timestamp`
- **DEFS** — variable definitions: `var := expr`
- **CONSTRAINTS** — arithmetic constraints

A file must have at least one BUS or MEM section. All bus interactions must have the same arity. Integer literals can be used directly in bus/mem definitions. BUS and MEM are matched independently.

### BUS Example

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

**BUS:** Two bus interactions balance when their multiplicities sum to 0 and all corresponding arguments are equal. A bus can self-balance when its multiplicity is 0 (no argument constraints imposed).

**MEM:** Pairwise matching works the same as BUS. Self-balancing is extended:
- `mul == 0` — disabled (same as BUS).
- `mul == -1` — self-balanced input: requires `timestamp < TS_ENTRY`; pairwise distinct timestamps and distinct `(address_space, pointer)` across all self-balanced inputs.
- `mul == 1` — self-balanced output: pairwise distinct timestamps and distinct `(address_space, pointer)` across all self-balanced outputs.

When MEM interactions are present, a free variable `TS_ENTRY` is automatically injected.

A set of interactions is balanced if it can be partitioned into balanced pairs (within each pool).

## SMT Encoding

1. Definitions are encoded as equalities (`var == expr`).
2. Constraints are encoded directly.
3. BUS matching:
   - For each pair `(i, j)`: Boolean `m_i_j` with axioms `m_i_j => mul_i + mul_j == 0` and `m_i_j => arg_k_i == arg_k_j`.
   - For each bus `i`: self-match Boolean `m_i_i` with axiom `m_i_i => mul_i == 0`.
   - Per bus: `AtMost(..., 1)` and `AtLeast(..., 1)` over all its match variables.
4. MEM matching (prefix `mm_`): same pairwise scheme, plus:
   - Self-match axiom relaxed: `mm_i_i => mul_i ∈ {-1, 0, 1}`.
   - Input self-balancing: `(mm_i_i ∧ mul_i == -1) => ts_i < TS_ENTRY`.
   - Pairwise distinct inputs: `ts_i ≠ ts_j` and `¬(as_i == as_j ∧ ptr_i == ptr_j)`.
   - Pairwise distinct outputs: same constraints for `mul == 1`.

## Architecture

```
Input File → Parser → BusatProblem → Encoder → Z3 Constraints → Solver → Result
```

- `parser.py` — parses `.bus` files into `BusatProblem` dataclass (`BusInteraction`, `MemInteraction`) using Python `ast` module for expressions
- `encoder.py` — translates `BusatProblem` to Z3 constraints; BUS matching via `_encode_matching_group`, MEM self-balancing via `_encode_mem_self_balancing`
- `solver.py` — Z3 solver wrapper, `solve_from_file()` pipeline, `encode_from_file()` for SMT output
- `cli.py` — Click CLI with `solve` command

## CLI

```bash
busat solve <input.bus> [--timeout N] [-o output.json] [--show-model] [--encode-only] [-v]
```

Exit codes: 0 = sat, 1 = unsat, 2 = error/unknown.
