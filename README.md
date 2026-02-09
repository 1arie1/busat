# BUSAT

A Python CLI tool for SAT solving using the Z3 SMT solver.

## Installation

```bash
# Install in development mode
pip install -e .

# Or install with dev dependencies
pip install -e ".[dev]"
```

## Usage

```bash
busat --help
```

## Development

### Setup

```bash
# Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# Install in development mode with dev dependencies
pip install -e ".[dev]"
```

### Running Tests

```bash
pytest
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
├── src/
│   └── busat/
│       ├── __init__.py
│       ├── __main__.py
│       ├── cli.py
│       └── solver.py
├── tests/
│   └── test_busat.py
├── pyproject.toml
├── AGENT.md
└── README.md
```

## License

[TO BE SPECIFIED]
