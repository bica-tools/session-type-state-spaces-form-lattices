"""Grammar conformance: the reticulate AST must match the authoritative grammar.

The single source of truth is ``docs/specs/grammar.yaml`` (derived from
``authoritative-grammar.md`` §1 / ICE 2026 main.tex §2.1). This test asserts
that the Python AST exposes exactly the grammar's constructors — no missing
nodes, and no ``forbidden`` drift nodes (e.g. ``Seq``).

This is both the ongoing drift gate and the v1.0.0 release gate: the extracted
corpus parser must pass it cleanly.
"""
from __future__ import annotations

import typing
from pathlib import Path

import pytest
import yaml

from reticulatep import parser


def _load_grammar() -> dict:
    """Locate docs/specs/grammar.yaml (monorepo) or a packaged copy (standalone)."""
    here = Path(__file__).resolve()
    candidates = []
    for parent in here.parents:
        candidates.append(parent / "docs" / "specs" / "grammar.yaml")
    candidates.append(Path(parser.__file__).resolve().parent / "grammar.yaml")
    for c in candidates:
        if c.is_file():
            return yaml.safe_load(c.read_text())
    raise FileNotFoundError("grammar.yaml not found (docs/specs/ or packaged)")


GRAMMAR = _load_grammar()


def _ast_node_names() -> set[str]:
    """The AST session-type node classes, taken from the `SessionType` union."""
    return {t.__name__ for t in typing.get_args(parser.SessionType)}


def test_every_grammar_constructor_has_an_ast_class():
    """Each of the six constructors maps to a class present in the AST union."""
    nodes = _ast_node_names()
    for c in GRAMMAR["constructors"]:
        cls = c["py"]
        assert hasattr(parser, cls), f"missing AST class {cls} for constructor {c['name']}"
        assert cls in nodes, f"{cls} not in SessionType union"


def test_declaration_classes_present():
    for cls in GRAMMAR["declaration"]["py"]:
        assert hasattr(parser, cls), f"missing declaration class {cls}"


def test_ast_union_matches_grammar_exactly():
    """The AST node set must equal the grammar constructors — no extras, no drift."""
    expected = {c["py"] for c in GRAMMAR["constructors"]}
    actual = _ast_node_names()
    forbidden = {f["py"] for f in GRAMMAR.get("forbidden", [])}

    present_drift = actual & forbidden
    assert not present_drift, f"forbidden drift nodes present: {sorted(present_drift)}"
    assert actual == expected, f"AST union {sorted(actual)} != grammar {sorted(expected)}"
