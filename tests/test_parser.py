"""Tests for the BUSAT parser."""

import pytest
from busat.parser import (
    parse_text,
    ParseError,
    BusInteraction,
    _split_sections,
    _parse_bus_section,
    _parse_defs_section,
    _parse_constraints_section,
)


class TestSplitSections:
    def test_all_sections(self) -> None:
        text = "BUS\n1: p, a\n\nDEFS\na := 1\n\nCONSTRAINTS\na > 0\n"
        sections = _split_sections(text)
        assert set(sections.keys()) == {"BUS", "DEFS", "CONSTRAINTS"}

    def test_bus_only(self) -> None:
        text = "BUS\n1: p, a\n"
        sections = _split_sections(text)
        assert "BUS" in sections
        assert "DEFS" not in sections

    def test_ignores_leading_text(self) -> None:
        text = "some preamble\nBUS\n1: p, a\n"
        sections = _split_sections(text)
        assert "BUS" in sections
        assert "1: p, a" in sections["BUS"]


class TestParseBusSection:
    def test_basic(self) -> None:
        buses = _parse_bus_section("1: p, a, b\n2: q, x, y\n")
        assert len(buses) == 2
        assert buses[0] == BusInteraction(id=1, multiplicity="p", arguments=["a", "b"])
        assert buses[1] == BusInteraction(id=2, multiplicity="q", arguments=["x", "y"])

    def test_skips_blank_and_comments(self) -> None:
        buses = _parse_bus_section("\n# comment\n1: p, a\n\n")
        assert len(buses) == 1

    def test_no_colon_raises(self) -> None:
        with pytest.raises(ParseError):
            _parse_bus_section("bad line")

    def test_non_int_id_raises(self) -> None:
        with pytest.raises(ParseError, match="integer"):
            _parse_bus_section("abc: p, a")

    def test_whitespace_handling(self) -> None:
        buses = _parse_bus_section("  1 :  p ,  a ,  b  \n")
        assert buses[0].multiplicity == "p"
        assert buses[0].arguments == ["a", "b"]


class TestParseDefsSection:
    def test_basic(self) -> None:
        defs = _parse_defs_section("a := b + 1\np := -1\n")
        assert len(defs) == 2
        assert defs[0].variable == "a"
        assert defs[0].expression == "b + 1"
        assert defs[1].variable == "p"

    def test_missing_assign_raises(self) -> None:
        with pytest.raises(ParseError, match=":="):
            _parse_defs_section("a = 1")

    def test_invalid_expression_raises(self) -> None:
        with pytest.raises(ParseError, match="invalid expression"):
            _parse_defs_section("a := +++")

    def test_invalid_varname_raises(self) -> None:
        with pytest.raises(ParseError, match="invalid variable"):
            _parse_defs_section("123 := 1")


class TestParseConstraintsSection:
    def test_basic(self) -> None:
        constraints = _parse_constraints_section("a > 0\nb >= 0\n")
        assert len(constraints) == 2
        assert constraints[0].expression == "a > 0"

    def test_chained_comparison(self) -> None:
        constraints = _parse_constraints_section("0 <= a < 10\n")
        assert len(constraints) == 1

    def test_invalid_syntax_raises(self) -> None:
        with pytest.raises(ParseError, match="invalid constraint"):
            _parse_constraints_section("a >< 0")


class TestParseText:
    def test_full_example(self) -> None:
        text = """\
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
"""
        problem = parse_text(text)
        assert len(problem.buses) == 2
        assert len(problem.definitions) == 4
        assert len(problem.constraints) == 3

    def test_missing_bus_section_raises(self) -> None:
        with pytest.raises(ParseError, match="missing BUS"):
            parse_text("DEFS\na := 1\n")

    def test_empty_bus_section_raises(self) -> None:
        with pytest.raises(ParseError, match="at least one bus"):
            parse_text("BUS\n\nDEFS\na := 1\n")

    def test_duplicate_bus_id_raises(self) -> None:
        with pytest.raises(ParseError, match="duplicate bus id"):
            parse_text("BUS\n1: p, a\n1: q, b\n")

    def test_inconsistent_arity_raises(self) -> None:
        with pytest.raises(ParseError, match="arguments"):
            parse_text("BUS\n1: p, a, b\n2: q, x\n")

    def test_duplicate_def_raises(self) -> None:
        with pytest.raises(ParseError, match="duplicate definition"):
            parse_text("BUS\n1: p, a\n\nDEFS\na := 1\na := 2\n")

    def test_no_defs_no_constraints(self) -> None:
        problem = parse_text("BUS\n1: p, a\n2: q, b\n")
        assert len(problem.definitions) == 0
        assert len(problem.constraints) == 0
