"""Command-line interface for BUSAT."""

import click
from busat import __version__


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
@click.pass_context
def solve(ctx: click.Context, input_file: str, timeout: int, output: str | None) -> None:
    """Solve a SAT problem from INPUT_FILE.

    Example:
        busat solve problem.smt2
    """
    verbose = ctx.obj["verbose"]
    if verbose:
        click.echo(f"Solving: {input_file}")
        click.echo(f"Timeout: {timeout}s")

    # TODO: Implement solver logic
    click.echo("Solver functionality not yet implemented.")
    click.echo("Please specify the behavior in AGENT.md")


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
