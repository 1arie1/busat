"""Integration tests for BUSAT."""

import json
from pathlib import Path

import pytest
from click.testing import CliRunner

from busat.cli import main
from busat.solver import solve_from_file, encode_from_file

FIXTURES = Path(__file__).parent / "fixtures"


class TestSolveFromFile:
    def test_simple_sat(self) -> None:
        result = solve_from_file(str(FIXTURES / "simple_sat.bus"))
        assert result["status"] == "sat"
        assert result["model"] is not None
        assert result["model"]["p"] == 1
        assert result["model"]["q"] == -1

    def test_simple_unsat(self) -> None:
        result = solve_from_file(str(FIXTURES / "simple_unsat.bus"))
        assert result["status"] == "unsat"
        assert result["model"] is None

    def test_multi_bus(self) -> None:
        result = solve_from_file(str(FIXTURES / "multi_bus.bus"))
        assert result["status"] == "sat"
        assert result["model"] is not None

    def test_no_defs(self) -> None:
        result = solve_from_file(str(FIXTURES / "no_defs.bus"))
        assert result["status"] == "sat"

    def test_no_constraints(self) -> None:
        result = solve_from_file(str(FIXTURES / "no_constraints.bus"))
        assert result["status"] == "sat"

    def test_bad_file(self, tmp_path: Path) -> None:
        bad = tmp_path / "bad.bus"
        bad.write_text("DEFS\na := 1\n")
        result = solve_from_file(str(bad))
        assert result["status"] == "error"
        assert "Parse error" in result["message"]


class TestCLI:
    def test_solve_sat(self) -> None:
        runner = CliRunner()
        result = runner.invoke(main, ["solve", str(FIXTURES / "simple_sat.bus")])
        assert result.exit_code == 0
        assert "SAT" in result.output

    def test_solve_unsat(self) -> None:
        runner = CliRunner()
        result = runner.invoke(main, ["solve", str(FIXTURES / "simple_unsat.bus")])
        assert result.exit_code == 1
        assert "UNSAT" in result.output

    def test_verbose_output(self) -> None:
        runner = CliRunner()
        result = runner.invoke(main, ["-v", "solve", str(FIXTURES / "simple_sat.bus")])
        assert result.exit_code == 0
        assert "Variable assignments:" in result.output
        assert "p = 1" in result.output

    def test_json_output(self, tmp_path: Path) -> None:
        out_file = tmp_path / "result.json"
        runner = CliRunner()
        result = runner.invoke(
            main, ["solve", str(FIXTURES / "simple_sat.bus"), "-o", str(out_file)]
        )
        assert result.exit_code == 0
        data = json.loads(out_file.read_text())
        assert data["status"] == "sat"
        assert isinstance(data["model"], dict)

    def test_error_exit_code(self, tmp_path: Path) -> None:
        bad = tmp_path / "bad.bus"
        bad.write_text("not valid")
        runner = CliRunner()
        result = runner.invoke(main, ["solve", str(bad)])
        assert result.exit_code == 2

    def test_nonexistent_file(self) -> None:
        runner = CliRunner()
        result = runner.invoke(main, ["solve", "/nonexistent/path.bus"])
        assert result.exit_code != 0

    def test_encode_only_stdout(self) -> None:
        runner = CliRunner()
        result = runner.invoke(
            main, ["solve", "--encode-only", str(FIXTURES / "simple_sat.bus")]
        )
        assert result.exit_code == 0
        assert "assert" in result.output or "declare-fun" in result.output

    def test_encode_only_to_file(self, tmp_path: Path) -> None:
        out_file = tmp_path / "formula.smt2"
        runner = CliRunner()
        result = runner.invoke(
            main,
            ["solve", "--encode-only", str(FIXTURES / "simple_sat.bus"), "-o", str(out_file)],
        )
        assert result.exit_code == 0
        content = out_file.read_text()
        assert len(content) > 0

    def test_encode_only_error(self, tmp_path: Path) -> None:
        bad = tmp_path / "bad.bus"
        bad.write_text("not valid")
        runner = CliRunner()
        result = runner.invoke(main, ["solve", "--encode-only", str(bad)])
        assert result.exit_code == 2


class TestEncodeFromFile:
    def test_returns_smtlib(self) -> None:
        smt = encode_from_file(str(FIXTURES / "simple_sat.bus"))
        assert isinstance(smt, str)
        assert len(smt) > 0

    def test_contains_declarations(self) -> None:
        smt = encode_from_file(str(FIXTURES / "simple_sat.bus"))
        # Should contain variable declarations or assertions
        assert "assert" in smt.lower() or "declare" in smt.lower()
