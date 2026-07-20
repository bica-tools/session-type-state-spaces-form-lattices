"""reticulate CLI — parse a session type and analyse its lattice state space."""
from __future__ import annotations

import argparse
import sys

from .parser import parse, ParseError, pretty
from .statespace import build_statespace
from .lattice import check_lattice
from .visualize import dot_source


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        prog="reticulate",
        description="Lattice analysis of session-type state spaces (ICE 2026).")
    ap.add_argument("type", help="session type, e.g. \'&{a: end, b: end}\'")
    ap.add_argument("--hasse", action="store_true", help="print the Hasse diagram (Graphviz DOT)")
    ap.add_argument("--pretty", action="store_true", help="pretty-print the parsed type and exit")
    args = ap.parse_args(argv)

    try:
        ast = parse(args.type)
    except ParseError as e:
        print(f"parse error: {e}", file=sys.stderr)
        return 2

    if args.pretty:
        print(pretty(ast))
        return 0

    ss = build_statespace(ast)
    if args.hasse:
        print(dot_source(ss))
        return 0

    res = check_lattice(ss)
    print(f"states={len(ss.states)} transitions={len(ss.transitions)} sccs={res.num_scc}")
    print(f"lattice={res.is_lattice} (top={res.has_top} bottom={res.has_bottom} "
          f"meets={res.all_meets_exist} joins={res.all_joins_exist})")
    return 0 if res.is_lattice else 1


if __name__ == "__main__":
    raise SystemExit(main())
