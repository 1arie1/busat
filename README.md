# 🚌 BUSAT

A Python CLI tool for solving pairwise satisfiability of bus interaction constraints from OpenVM using the Z3 SMT solver.

BUSAT takes a list of bus interactions, variable definitions, and arithmetic constraints, then determines whether the bus interactions can be balanced pairwise (by matching multiplicities) and outputs a satisfying assignment.

## Installation

```bash
# Create virtual environment
python -m venv venv
source venv/bin/activate

# Install in development mode
pip install -e ".[dev]"
```

## 🚏 Input Format

Input files (`.bus`) have three sections:

- **BUS** — bus interactions: `id: multiplicity, arg1, arg2, ...`
- **DEFS** — variable definitions: `var := expression`
- **CONSTRAINTS** — arithmetic constraints: `expression`

Two bus interactions balance when their multiplicities sum to 0 and all corresponding arguments are equal. A bus can also self-balance when its multiplicity is 0. BUSAT checks whether all buses can be partitioned into balanced pairs. 🚌💨

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
3. **Bus matching** uses Boolean indicator variables:
   - For each pair of buses `(i, j)`, a Boolean `m_i_j` indicates they are matched.
   - `m_i_j => mul_i + mul_j == 0` — multiplicities must cancel.
   - `m_i_j => arg_k_i == arg_k_j` — all corresponding arguments must be equal.
   - For each bus `i`, a self-match Boolean `m_i_i` allows it to balance alone: `m_i_i => mul_i == 0` (no argument constraints).
   - Per bus, pseudo-Boolean constraints `AtMost(..., 1)` and `AtLeast(..., 1)` ensure exactly one match.

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
