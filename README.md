# 🚌 BUSAT

A Python CLI tool for solving pairwise satisfiability of bus and memory interaction constraints from OpenVM using the Z3 SMT solver.

BUSAT takes a list of bus/memory interactions, variable definitions, and arithmetic constraints, then determines whether the interactions can be balanced pairwise (by matching multiplicities) and outputs a satisfying assignment.

## Installation

```bash
# Create virtual environment
python -m venv venv
source venv/bin/activate

# Install in development mode
pip install -e ".[dev]"
```

## 🚏 Input Format

Input files (`.bus`) have up to four sections:

- **BUS** — bus interactions: `id: multiplicity, arg1, arg2, ...`
- **MEM** — memory bus interactions: `id: multiplicity, address_space, pointer, b0, b1, b2, b3, timestamp`
- **DEFS** — variable definitions: `var := expression`
- **CONSTRAINTS** — arithmetic constraints: `expression`

A file must have at least one **BUS** or **MEM** section. BUS and MEM interactions are matched independently within their own pools.

### Balancing Rules

**BUS interactions** balance when their multiplicities sum to 0 and all corresponding arguments are equal. A bus can self-balance when its multiplicity is 0. BUSAT checks whether all buses can be partitioned into balanced pairs. 🚌💨

**MEM interactions** follow the same pairwise matching rules, plus additional self-balancing modes:

| Self-match mul | Meaning | Extra constraints |
|---|---|---|
| `0` | Disabled (no-op) | None |
| `-1` | Self-balanced input | `timestamp < TS_ENTRY`; pairwise: distinct timestamps and distinct `(address_space, pointer)` across all self-balanced inputs |
| `1` | Self-balanced output | Pairwise: distinct timestamps and distinct `(address_space, pointer)` across all self-balanced outputs |

When MEM interactions are present, a free variable `TS_ENTRY` is automatically injected and can be used in DEFS/CONSTRAINTS.

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

### MEM Example

```
MEM
1: p, as1, ptr1, b0_1, b1_1, b2_1, b3_1, ts1
2: q, as2, ptr2, b0_2, b1_2, b2_2, b3_2, ts2

DEFS
p := 1
q := -1
as1 := 1
as2 := 1
ptr1 := 100
ptr2 := 100
b0_1 := 10
b0_2 := 10
b1_1 := 20
b1_2 := 20
b2_1 := 30
b2_2 := 30
b3_1 := 40
b3_2 := 40
ts1 := 5
ts2 := 5
```

## 🚌 Usage

```bash
# Solve a problem (exit code: 0=sat, 1=unsat, 2=error)
busat solve problem.bus

# Show bus matching and variable assignments
busat solve problem.bus --show-model

# Verbose output
busat solve -v problem.bus

# Write results as JSON
busat solve problem.bus -o result.json

# Output encoded SMT formula without solving
busat solve --encode-only problem.bus
```

### Example output

```
$ busat solve tests/fixtures/simple_sat.bus --show-model
SAT — satisfying assignment found
Bus matching:
  bus 1 <-> bus 2
Variable assignments:
  a = 1
  b = 0
  c = 2
  p = 1
  q = -1
  x = 1
  y = 0
  z = 2
```

## 🔧 SMT Encoding

BUSAT translates the bus matching problem into an SMT formula over integer arithmetic and Booleans:

1. **Definitions** become equalities: `a := b + 1` encodes as `a == b + 1`.
2. **Constraints** are translated directly into Z3 comparisons.
3. **BUS matching** uses Boolean indicator variables:
   - For each pair of buses `(i, j)`, a Boolean `m_i_j` indicates they are matched.
   - `m_i_j => mul_i + mul_j == 0` — multiplicities must cancel.
   - `m_i_j => arg_k_i == arg_k_j` — all corresponding arguments must be equal.
   - For each bus `i`, a self-match Boolean `m_i_i` allows it to balance alone: `m_i_i => mul_i == 0` (no argument constraints).
   - Per bus, pseudo-Boolean constraints `AtMost(..., 1)` and `AtLeast(..., 1)` ensure exactly one match.
4. **MEM matching** uses the same pairwise scheme (with prefix `mm_`), plus:
   - Self-match axiom is relaxed: `mm_i_i => mul_i ∈ {-1, 0, 1}`.
   - **Input self-balancing** (`mm_i_i ∧ mul_i == -1`): `ts_i < TS_ENTRY`.
   - **Pairwise distinct inputs**: for two self-balanced inputs `i, j`: `ts_i ≠ ts_j` and `¬(as_i == as_j ∧ ptr_i == ptr_j)`.
   - **Pairwise distinct outputs**: same constraints for self-balanced outputs (`mul == 1`).

Use `--encode-only` to inspect the generated SMT-LIB formula.

## Development

### Running Tests

```bash
pytest tests/ -v
```

### Code Formatting

```bash
black src/ tests/
```

### Type Checking

```bash
mypy src/
```

## Project Structure

```
busat/
├── src/busat/
│   ├── __init__.py      # Package version
│   ├── __main__.py      # python -m busat entry point
│   ├── cli.py           # Click CLI (solve command)
│   ├── parser.py        # .bus file parser
│   ├── encoder.py       # Z3 constraint encoder
│   └── solver.py        # Z3 solver wrapper
├── tests/
│   ├── fixtures/        # .bus test fixtures
│   ├── test_busat.py    # Basic solver tests
│   ├── test_parser.py   # Parser unit tests
│   ├── test_encoder.py  # Encoder unit tests
│   └── test_integration.py  # End-to-end and CLI tests
├── pyproject.toml
├── AGENT.md
└── README.md
```

## Authors

- 🧑‍💻 Arie Gurfinkel
- 🤖 Claude Code

## License

MIT
