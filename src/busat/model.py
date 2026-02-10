"""Model display utilities for BUSAT results."""

from __future__ import annotations


def format_matching(label: str, matching: list[list[int]]) -> str:
    """Format a matching group (bus or mem) as a string."""
    lines = [f"{label} matching:"]
    tag = label.lower()
    for id_a, id_b in matching:
        if id_a == id_b:
            lines.append(f"  {tag} {id_a} <-> self (multiplicity = 0)")
        else:
            lines.append(f"  {tag} {id_a} <-> {tag} {id_b}")
    return "\n".join(lines)


def format_variables(model: dict[str, int]) -> str:
    """Format variable assignments as a string."""
    lines = ["Variable assignments:"]
    for name, val in sorted(model.items()):
        lines.append(f"  {name} = {val}")
    return "\n".join(lines)


def format_model(result: dict[str, object]) -> str:
    """Format full model: matchings and variable assignments."""
    parts: list[str] = []
    if result.get("matching"):
        parts.append(format_matching("Bus", result["matching"]))  # type: ignore[arg-type]
    if result.get("mem_matching"):
        parts.append(format_matching("Mem", result["mem_matching"]))  # type: ignore[arg-type]
    if result.get("model"):
        parts.append(format_variables(result["model"]))  # type: ignore[arg-type]
    return "\n".join(parts)
