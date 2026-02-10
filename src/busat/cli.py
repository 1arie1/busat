"""Command-line interface for BUSAT."""

import json
import sys

import click
from busat import __version__
from busat.model import format_model, format_variables
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
@click.option("--show-model", is_flag=True, help="Print bus matching and variable assignments")
@click.pass_context
def solve(
    ctx: click.Context,
    input_file: str,
    timeout: int,
    output: str | None,
    encode_only: bool,
    show_model: bool,
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

    if result["status"] == "sat":
        if show_model:
            click.echo(format_model(result))
        elif verbose and result["model"]:
            click.echo(format_variables(result["model"]))

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


if __name__ == "__main__":
    main()
