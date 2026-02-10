"""Model display utilities for BUSAT results."""

from __future__ import annotations

_MEM_SELF_LABELS: dict[int, str] = {
    -1: "input",
    0: "disabled",
    1: "output",
}


def format_matching(label: str, matching: list[tuple[int, ...]] | list[list[int]]) -> str:
    """Format a matching group (bus or mem) as a string."""
    lines = [f"{label} matching:"]
    tag = label.lower()
    for entry in matching:
        id_a, id_b = entry[0], entry[1]
        if id_a == id_b:
            lines.append(f"  {tag} {id_a} <-> self (multiplicity = 0)")
        else:
            lines.append(f"  {tag} {id_a} <-> {tag} {id_b}")
    return "\n".join(lines)


def format_mem_matching(matching: list[tuple[int, int, int | None]] | list[list[int]]) -> str:
    """Format a MEM matching group, showing self-balance type."""
    lines = ["Mem matching:"]
    for entry in matching:
        id_a, id_b = entry[0], entry[1]
        mul = entry[2] if len(entry) > 2 else None
        if id_a == id_b:
            kind = _MEM_SELF_LABELS.get(mul, f"multiplicity = {mul}") if mul is not None else "multiplicity = 0"
            lines.append(f"  mem {id_a} <-> self ({kind})")
        else:
            lines.append(f"  mem {id_a} <-> mem {id_b}")
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
        parts.append(format_mem_matching(result["mem_matching"]))  # type: ignore[arg-type]
    if result.get("model"):
        parts.append(format_variables(result["model"]))  # type: ignore[arg-type]
    return "\n".join(parts)
