# BUSAT - Agent Specification

## Overview
BUSAT is a Python CLI tool for solving pariwise satisfiability of bus interaction constraints from OpenVM. 


## Purpose

BuSat takes a list of bus interaction, variable definitions, and arithmetic constraints (eventually arbitrary SMT constraints can be supported). It then decides whether there bus interactions can be balanced pairwise (i.e., by matching multiplicities), and if so, outputs a satisfying assignment.
## Technical Requirements

### Input Format

The input is a text file that specifies (a) bus interactions, (b) variable definitions, and (c) additional constraints. For example

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

Where a bus interaction is defined by a numeric identifier and sequence of arguments. The first argument is a multiplicity. The other arguments are variables. ALl bus interactions have same arity. A multiplicity is a symbolic expression that evaluates to either -1, 0, or 1.

For example, the line
```
1: p, a, b, c
```
defines a bus interaction with id of 1, multiplicity p, and arguments `(a, b, c)`


### Output Format

The tool constructs an SMT formula that encodes whether all bus interactions in the input file balance, and all variables satisfy the additional constraints.

Two bus interactions balance if their multiplicity cancel out (i.e., add up to 0). A set of bus interactions is balanced if the set can be partitioned into a set of pairs so that every pair of interactions that are grouped together balance.

When two bus interaction balance, their arguments (other than multiplicity) must be equal. 

For example, consider two bus interactions 1 and 2 bellow:
```
1: p, a, b, c
2: q, x, y, z
```

They balance when `p + q == 0` and `a == x`, `b == y`, and `c == z`.


In the constructed SMT formula:

    1. the constraints are encoded directly into SMT
    2. definitions are encoded as equalities in SMT
    3. bus interactions are encoded using the following algorithm strategy:
       1. for every pair of busses `i`, `j`, introduce a Boolean variable `m_i_j` 
       2. intuitively, `m_i_j` is true iff bus `i` is balanced with bus `j`
       3. add axioms `m_i_j ==> bus_i[mul] + bus_j[mul] == 0`
       4. add axiom `m_i_j ==> bus_i[arg_k] == bus_j[arg_k]` for every argument of the bus
       5. add pseudo boolean constraint `at_most({m_i_j}, 1)` to ensure that at most one `m_i_j` variable is true
       6. add pseudo boolean constraint `at_least({m_i_j}, 1)` to ensure that at least one `m_i_j` variable is true




### Z3 Integration
    Allow solving generated constraint using Z3

## Use Cases

### Use Case 1: [Name]
[TO BE SPECIFIED]

### Use Case 2: [Name]
[TO BE SPECIFIED]

## Command Structure

```bash
busat [OPTIONS] COMMAND [ARGS]...
```

### Commands
[TO BE SPECIFIED]

Example:
- `busat solve <input-file>` - Solve a SAT problem
- `busat check <formula>` - Check satisfiability
- `busat optimize <constraints>` - Find optimal solution

### Options
[TO BE SPECIFIED]

Example:
- `--verbose` / `-v` - Enable verbose output
- `--timeout <seconds>` - Set solver timeout
- `--output <file>` - Specify output file

## Examples

[ADD USAGE EXAMPLES HERE]

```bash
# Example 1
busat solve problem.smt2

# Example 2
busat check --formula "(and (> x 0) (< x 10))"
```

## Implementation Notes
[TO BE SPECIFIED]

- Architecture decisions
- Module structure
- Error handling approach
- Testing strategy
