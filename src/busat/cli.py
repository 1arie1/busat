"""Command-line interface for BUSAT."""

import json
import sys

import click
from busat import __version__
from busat.solver import solve_from_file, encode_from_file


@click.group()
@click.version_option(version=__version__)
@click.option("--verbose", "-v", is_flag=True, help="Enable verbose output")
@click.pass_context
def main(ctx: click.Context, verbose: bool) -> None:
    """BUSAT - A CLI tool for SAT solving using Z3.

    Use --help with any command to see available options.
    """
    ctx.ensure_object(dict)
    ctx.obj["verbose"] = verbose


@main.command()
@click.argument("input_file", type=click.Path(exists=True))
@click.option("--timeout", type=int, default=0, help="Solver timeout in seconds (0 = no limit)")
@click.option("--output", "-o", type=click.Path(), help="Output file path")
@click.option("--encode-only", is_flag=True, help="Print encoded SMT formula without solving")
@click.pass_context
def solve(
    ctx: click.Context,
    input_file: str,
    timeout: int,
    output: str | None,
    encode_only: bool,
) -> None:
    """Solve a bus matching problem from INPUT_FILE.

    Example:
        busat solve problem.bus
    """
    verbose = ctx.obj["verbose"]

    if encode_only:
        try:
            smt = encode_from_file(input_file)
        except Exception as e:
            click.echo(f"Error: {e}", err=True)
            sys.exit(2)
        if output:
            with open(output, "w") as f:
                f.write(smt)
            if verbose:
                click.echo(f"SMT formula written to {output}")
        else:
            click.echo(smt)
        sys.exit(0)

    if verbose:
        click.echo(f"Solving: {input_file}")
        if timeout:
            click.echo(f"Timeout: {timeout}s")

    result = solve_from_file(input_file, timeout=timeout)

    click.echo(result["message"])

    if verbose and result["status"] == "sat" and result["model"]:
        click.echo("Variable assignments:")
        for name, val in sorted(result["model"].items()):
            click.echo(f"  {name} = {val}")

    if output:
        with open(output, "w") as f:
            json.dump(result, f, indent=2)
        if verbose:
            click.echo(f"Results written to {output}")

    if result["status"] == "sat":
        sys.exit(0)
    elif result["status"] == "unsat":
        sys.exit(1)
    else:
        sys.exit(2)


@main.command()
@click.option("--formula", "-f", required=True, help="Formula to check")
@click.pass_context
def check(ctx: click.Context, formula: str) -> None:
    """Check satisfiability of a formula.

    Example:
        busat check --formula "(and (> x 0) (< x 10))"
    """
    verbose = ctx.obj["verbose"]
    if verbose:
        click.echo(f"Checking formula: {formula}")

    # TODO: Implement check logic
    click.echo("Check functionality not yet implemented.")
    click.echo("Please specify the behavior in AGENT.md")


if __name__ == "__main__":
    main()
