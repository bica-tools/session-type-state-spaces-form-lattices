"""Session type parser: AST nodes, tokenizer, recursive-descent parser, pretty-printer.

Core Grammar
------------

::

    S  ::=  &{ m₁ : S₁ , … , mₙ : Sₙ }    -- branch (external choice)
         |  +{ l₁ : S₁ , … , lₙ : Sₙ }    -- selection (internal choice)
         |  S₁ || S₂                        -- parallel composition
         |  S₁ . S₂                          -- continuation (after parallel)
         |  rec X . S                        -- recursion
         |  ( S )                            -- grouping
         |  X                                -- type variable
         |  end                              -- session terminated

Precedence (tightest first): ``.`` > ``||``.

Sequential composition (``.``): if the left operand is a bare identifier
``m``, ``m . S`` is **parser-level sugar** for the singleton-branch
``&{m: S}`` (no separate AST node — see
``docs/specs/authoritative-grammar.md`` §1+§2). Otherwise the `.`
produces the deprecated ``Seq(S₁, S₂)`` (transitional drift per §2).

Step 14a (2026-04-16): The ``wait`` terminal was retired from the
grammar. Under pre-14a semantics ``wait`` signalled a parallel-branch
barrier and state-spaced to the same sink as ``end``; the distinction
was syntactic only. The new grammar pushes the synchronisation
semantics into ``Par``'s state-space construction (see
``docs/specs/parallel-wait-sync-spec.md``). A decidable well-formedness
predicate ``is_wellformed_new`` now rejects the obviously-degenerate
pattern ``(end || end) . S`` that previously required ``wait``.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum, auto
from typing import Union


# ---------------------------------------------------------------------------
# AST nodes (frozen dataclasses, hashable)
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class End:
    """Terminated session — no further method calls permitted."""


@dataclass(frozen=True)
class Var:
    """Type variable reference (e.g. ``X`` inside ``rec X . …``)."""
    name: str


@dataclass(frozen=True)
class Branch:
    """External choice ``&{ m₁ : S₁ , … , mₙ : Sₙ }``."""
    choices: tuple[tuple[str, "SessionType"], ...]


@dataclass(frozen=True)
class Select:
    """Internal choice ``+{ l₁ : S₁ , … , lₙ : Sₙ }``."""
    choices: tuple[tuple[str, "SessionType"], ...]


@dataclass(frozen=True)
class Parallel:
    """N-ary parallel composition ``S₁ || S₂ || … || Sₙ``."""
    branches: tuple["SessionType", ...]


@dataclass(frozen=True)
class Rec:
    """Recursive type ``rec X . S``."""
    var: str
    body: "SessionType"


@dataclass(frozen=True)
class Seq:
    """Deprecated: **general sequential composition** ``S₁ . S₂``.

    ``Seq(left, right)`` is the arity-2 sequential-composition
    primitive with no label.  Lattice semantics: ordinal sum
    ``L(Seq(S₁, S₂)) = L(S₁) ⊕ L(S₂)`` — the top of the left
    lattice is glued to the bottom of the right lattice.

    .. deprecated:: 2026-05-17 (chain-as-sugar audit)
       The authoritative grammar (``docs/specs/authoritative-grammar.md``
       §1) has six constructors and no `Seq`; the `(S₁ ∥ S₂) . T`
       pattern that motivated `Seq` is listed in §2 as
       non-conformant drift retained only transitionally for
       backward-compatibility of pre-2026-05-17 protocol files.
       Phase 1d of the chain-as-sugar sweep retired the `Chain`
       node; `Seq` is the next candidate for retirement (Phase 2+).
       New code MUST NOT introduce ``Seq`` nodes.
    """
    left: "SessionType"
    right: "SessionType"


# Deprecated aliases — kept for one release cycle (T2b migration).
Continuation = Seq
Sequence = Seq


SessionType = Union[
    End, Var, Branch, Select, Parallel, Rec
]


# ---------------------------------------------------------------------------
# Equation grammar: named definitions
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class Definition:
    """Named type definition: Name = S"""
    name: str
    body: SessionType


@dataclass(frozen=True)
class Program:
    """A sequence of named definitions. First definition is the entry point."""
    definitions: tuple[Definition, ...]


# ---------------------------------------------------------------------------
# Tokenizer
# ---------------------------------------------------------------------------

class TokenKind(Enum):
    LBRACE = auto()    # {
    RBRACE = auto()    # }
    LPAREN = auto()    # (
    RPAREN = auto()    # )
    AMPERSAND = auto() # &
    PLUS = auto()      # +
    COLON = auto()     # :
    COMMA = auto()     # ,
    DOT = auto()       # .
    PAR = auto()       # ||
    EQUALS = auto()    # =
    IDENT = auto()     # identifier or keyword (end, rec)
    EOF = auto()


@dataclass(frozen=True)
class Token:
    kind: TokenKind
    value: str
    pos: int


class ParseError(Exception):
    """Raised on invalid session-type syntax, with character position."""

    def __init__(self, message: str, pos: int | None = None) -> None:
        self.pos = pos
        if pos is not None:
            message = f"at position {pos}: {message}"
        super().__init__(message)


def tokenize(source: str) -> list[Token]:
    """Scan *source* into a list of ``Token``s (including a trailing ``EOF``)."""
    tokens: list[Token] = []
    i = 0
    n = len(source)

    while i < n:
        ch = source[i]

        # skip whitespace
        if ch in " \t\n\r":
            i += 1
            continue

        # two-character token: ||
        if ch == "|" and i + 1 < n and source[i + 1] == "|":
            tokens.append(Token(TokenKind.PAR, "||", i))
            i += 2
            continue

        # single-character tokens
        single = {
            "{": TokenKind.LBRACE,
            "}": TokenKind.RBRACE,
            "(": TokenKind.LPAREN,
            ")": TokenKind.RPAREN,
            "&": TokenKind.AMPERSAND,
            "+": TokenKind.PLUS,
            ":": TokenKind.COLON,
            ",": TokenKind.COMMA,
            ".": TokenKind.DOT,
            "=": TokenKind.EQUALS,
        }
        if ch in single:
            tokens.append(Token(single[ch], ch, i))
            i += 1
            continue

        # Unicode alternatives (checked before general identifier scan
        # because μ, ⊕, ∥ all satisfy ch.isalpha() in Python)
        if ch == "\u2295":  # ⊕
            tokens.append(Token(TokenKind.PLUS, "\u2295", i))
            i += 1
            continue
        if ch == "\u2225":  # ∥
            tokens.append(Token(TokenKind.PAR, "\u2225", i))
            i += 1
            continue
        if ch == "\u03bc":  # μ
            tokens.append(Token(TokenKind.IDENT, "rec", i))
            i += 1
            continue

        # identifiers: [A-Za-z_][A-Za-z0-9_]*
        if ch.isalpha() or ch == "_":
            start = i
            while i < n and (source[i].isalnum() or source[i] == "_"):
                i += 1
            word = source[start:i]
            tokens.append(Token(TokenKind.IDENT, word, start))
            continue

        raise ParseError(f"unexpected character {ch!r}", i)

    tokens.append(Token(TokenKind.EOF, "", n))
    return tokens


# ---------------------------------------------------------------------------
# Recursive-descent parser
# ---------------------------------------------------------------------------

class _Parser:
    """Internal parser state."""

    def __init__(self, tokens: list[Token]) -> None:
        self._tokens = tokens
        self._pos = 0

    # -- helpers -------------------------------------------------------------

    def _peek(self) -> Token:
        return self._tokens[self._pos]

    def _advance(self) -> Token:
        tok = self._tokens[self._pos]
        self._pos += 1
        return tok

    def _expect(self, kind: TokenKind, context: str = "") -> Token:
        tok = self._peek()
        if tok.kind is not kind:
            ctx = f" ({context})" if context else ""
            raise ParseError(
                f"expected {kind.name}, got {tok.kind.name} ({tok.value!r}){ctx}",
                tok.pos,
            )
        return self._advance()

    # -- grammar rules -------------------------------------------------------

    def parse(self) -> SessionType:
        result = self._par_expr()
        if self._peek().kind is not TokenKind.EOF:
            tok = self._peek()
            raise ParseError(
                f"unexpected token {tok.kind.name} ({tok.value!r}) after expression",
                tok.pos,
            )
        return result

    def _par_expr(self) -> SessionType:
        """Parse parallel (lowest precedence, n-ary flat collection)."""
        first = self._cont_expr()

        if self._peek().kind is not TokenKind.PAR:
            return first

        parts: list[SessionType] = [first]
        while self._peek().kind is TokenKind.PAR:
            self._advance()  # consume '||'
            parts.append(self._cont_expr())

        return Parallel(tuple(parts))

    def _cont_expr(self) -> SessionType:
        """Parse continuation ``.`` (binds tighter than ``||``).

        Desugaring (chain-as-sugar, 2026-05-17):

        - If the left operand is a bare identifier ``m`` (parsed
          as ``Var(m)``), the `.` is interpreted as ``&{m: right}``
          — a singleton-method branch. `m . S` is **parser-level
          sugar** for the paper-grammar form `&{m: S}`; no `Chain`
          AST node is produced. The grammar (six constructors;
          `docs/specs/authoritative-grammar.md` §1) has no chain
          primitive — see §2 of that spec for the rationale.

        - Otherwise (the left is a `Parallel`, a grouped
          expression, etc.), the `.` is interpreted as the
          deprecated ``Seq(left, right)``. Per `authoritative-
          grammar.md` §2, `(S₁ ∥ S₂) . T` is non-conformant drift
          retained only for backward compatibility of pre-v2
          protocol files; reject in new artefacts.
        """
        left = self._atom()

        if self._peek().kind is TokenKind.DOT:
            self._advance()  # consume '.'
            right = self._cont_expr()  # right-associative
            if isinstance(left, Var):
                # m . S  ≡  &{m: S}  (parser-level sugar; no Chain AST node)
                return Branch(((left.name, right),))
            # parallel-with-continuation `(S₁ ∥ S₂) . T` is not in §2.1 — reject.
            raise ParseError(
                "parallel-with-continuation `(… ∥ …) . T` is not in the §2.1 grammar",
                self._peek().pos,
            )

        return left

    def _atom(self) -> SessionType:
        """Parse a self-delimiting construct."""
        tok = self._peek()

        # &{ ... }
        if tok.kind is TokenKind.AMPERSAND:
            return self._branch()

        # +{ ... } or ⊕{ ... }
        if tok.kind is TokenKind.PLUS:
            return self._select()

        # ( ... )  — grouping
        if tok.kind is TokenKind.LPAREN:
            return self._paren()

        # rec X . S
        if tok.kind is TokenKind.IDENT and tok.value == "rec":
            return self._rec()

        # end
        if tok.kind is TokenKind.IDENT and tok.value == "end":
            self._advance()
            return End()

        # plain identifier (type variable)
        if tok.kind is TokenKind.IDENT:
            self._advance()
            return Var(tok.value)

        raise ParseError(
            f"unexpected token {tok.kind.name} ({tok.value!r})", tok.pos
        )

    def _choice_list(self, context: str) -> tuple[tuple[str, SessionType], ...]:
        """Parse ``m₁ : S₁ , … , mₙ : Sₙ`` inside braces."""
        entries: list[tuple[str, SessionType]] = []
        while True:
            label_tok = self._expect(TokenKind.IDENT, f"{context} label")
            self._expect(TokenKind.COLON, f"{context} colon after {label_tok.value!r}")
            body = self._par_expr()
            entries.append((label_tok.value, body))
            if self._peek().kind is TokenKind.COMMA:
                self._advance()
            else:
                break
        return tuple(entries)

    def _branch(self) -> Branch:
        # Paper grammar allows n >= 0 (revised/main.tex L250-258). The
        # empty branch &{} is a valid surface form; its state space is
        # the 2-element lattice {q_0, q_⊥} per the construction in
        # Reticulate/Spec/StateSpace.lean Approach 2.
        self._advance()  # consume '&'
        self._expect(TokenKind.LBRACE, "branch")
        if self._peek().kind is TokenKind.RBRACE:
            self._advance()
            return Branch(())
        choices = self._choice_list("branch")
        self._expect(TokenKind.RBRACE, "branch closing")
        return Branch(choices)

    def _select(self) -> Select:
        # Symmetric to _branch — preserves branch/selection duality at
        # the n=0 boundary (paper L257-258).
        self._advance()  # consume '+'
        self._expect(TokenKind.LBRACE, "select")
        if self._peek().kind is TokenKind.RBRACE:
            self._advance()
            return Select(())
        choices = self._choice_list("select")
        self._expect(TokenKind.RBRACE, "select closing")
        return Select(choices)

    def _paren(self) -> SessionType:
        """Parse a parenthesized expression ``( S )``."""
        self._advance()  # consume '('
        inner = self._par_expr()
        self._expect(TokenKind.RPAREN, "closing ')'")
        return inner

    def _rec(self) -> Rec:
        self._advance()  # consume 'rec'
        var_tok = self._expect(TokenKind.IDENT, "recursion variable")
        if var_tok.value in ("rec", "end"):
            raise ParseError(
                f"{var_tok.value!r} is a keyword, not a valid variable name",
                var_tok.pos,
            )
        self._expect(TokenKind.DOT, "recursion dot")
        body = self._atom()
        return Rec(var_tok.value, body)


def parse(source: str) -> SessionType:
    """Parse a session-type string into an AST.

    Raises ``ParseError`` on invalid syntax, including new-grammar
    rejection of degenerate ``(end || end) . _`` patterns (see
    :func:`is_wellformed_new`).

    Examples::

        >>> parse("end")
        End()
        >>> parse("&{m: end}")
        Branch(choices=(('m', End()),))
    """
    tokens = tokenize(source)
    ast = _Parser(tokens).parse()
    _enforce_wellformed_new(ast)
    return ast


# ---------------------------------------------------------------------------
# Step 14a well-formedness: reject terminal-``end`` inside
# ``(_ || _) . _`` contexts.
# ---------------------------------------------------------------------------

def _ends_in_end(node: "SessionType") -> bool:
    """Structural ``ends-in-End`` check used by :func:`is_wellformed_new`.

    A node "structurally ends in ``End``" only when it performs no
    protocol work before terminating — i.e. it reduces to ``End`` at
    the top level (possibly through a pass-through ``Seq`` whose right
    operand is End, or a ``Rec`` whose body is End).

    Notably excluded:
    - ``Branch`` / ``Select`` (branching is real protocol work — this
      covers the singleton-Branch chain-sugar form too: a method call
      is real work even if the continuation is ``End``);
    - ``Var`` (a rec-bound variable keeps the loop live);
    - ``Parallel`` (parallel composition is real work).

    Cases:
    - ``End``                 → True
    - ``Seq(_, right)``       → True iff ``right`` ends in End
    - ``Rec(_, body)``        → True iff ``body`` ends in End (a
      degenerate rec whose body reduces to End).
    - Everything else         → False
    """
    match node:
        case End():
            return True
        case Seq(right=right):
            return _ends_in_end(right)
        case Rec(body=body):
            return _ends_in_end(body)
    return False


def _find_offending_seq_parallel(
    node: "SessionType",
) -> "Seq | None":
    """Locate the first ``Seq(Parallel(_, _), _)`` whose parallel has
    a branch structurally ending in ``End``.  Returns that ``Seq`` node
    or ``None`` if the AST is well-formed.
    """
    match node:
        case End() | Var():
            return None
        case Branch(choices=choices) | Select(choices=choices):
            for _, body in choices:
                r = _find_offending_seq_parallel(body)
                if r is not None:
                    return r
            return None
        case Rec(body=body):
            return _find_offending_seq_parallel(body)
        case Parallel(branches=branches):
            for b in branches:
                r = _find_offending_seq_parallel(b)
                if r is not None:
                    return r
            return None
        case Seq(left=left, right=right):
            # Check this Seq first: is left a Parallel with any branch
            # structurally ending in End?
            if isinstance(left, Parallel):
                for b in left.branches:
                    if _ends_in_end(b):
                        return node
            # Otherwise recurse.
            r = _find_offending_seq_parallel(left)
            if r is not None:
                return r
            return _find_offending_seq_parallel(right)
    return None


def is_wellformed_new(ast: "SessionType") -> bool:
    """Return ``True`` iff *ast* is well-formed under the Step 14a grammar.

    The single new-grammar constraint: for every
    ``Seq(Parallel(B1, ..., Bn), S)`` subterm, no ``Bᵢ`` may
    structurally terminate in ``End`` (see :func:`_ends_in_end` for
    the narrow structural definition).

    The narrow interpretation captures the degenerate cases where a
    parallel arm does no protocol work — ``end``, ``rec X . end``,
    ``m . end`` — while admitting realistic benchmarks whose branches
    perform method calls before (eventually) reaching ``End`` through
    nested ``Branch``/``Select`` nodes.

    This predicate closes the parallel-branch-barrier role that
    ``wait`` used to play in the retired pre-14a grammar.
    """
    return _find_offending_seq_parallel(ast) is None


def _enforce_wellformed_new(ast: "SessionType") -> None:
    """Raise ``ParseError`` if *ast* violates :func:`is_wellformed_new`."""
    offender = _find_offending_seq_parallel(ast)
    if offender is None:
        return
    snippet = pretty(offender)
    raise ParseError(
        "Step 14a well-formedness: a parallel branch inside "
        "`(... || ...) . S` structurally terminates in `end` (no "
        "reachable non-End path). This pattern used to be written "
        "with `wait`; under the new grammar it is ill-formed. "
        f"Offending subterm: {snippet!r}",
    )


# ---------------------------------------------------------------------------
# Pretty-printer
# ---------------------------------------------------------------------------

def pretty(node: SessionType) -> str:
    """Render an AST back to a human-readable session-type string.

    Parentheses are added around ``||`` only when needed for correct
    precedence (inside ``.`` or ``rec``).
    """
    return _pretty(node, in_tight=False)


def _pretty(node: SessionType, *, in_tight: bool) -> str:
    """Internal pretty-printer.

    *in_tight* is ``True`` when we are inside a context that binds tighter
    than ``||`` (i.e. inside ``.`` continuation or ``rec`` body).  In that
    case a ``Parallel`` node needs parentheses to roundtrip correctly.
    """
    match node:
        case End():
            return "end"
        case Var(name=name):
            return name
        case Branch(choices=choices):
            inner = ", ".join(
                f"{label}: {_pretty(body, in_tight=False)}"
                for label, body in choices
            )
            return f"&{{{inner}}}"
        case Select(choices=choices):
            inner = ", ".join(
                f"{label}: {_pretty(body, in_tight=False)}"
                for label, body in choices
            )
            return f"+{{{inner}}}"
        case Parallel(branches=branches):
            s = " || ".join(_pretty(b, in_tight=False) for b in branches)
            return f"({s})" if in_tight else s
        case Rec(var=var, body=body):
            return f"rec {var} . {_pretty(body, in_tight=True)}"
        case Seq(left=left, right=right):
            return f"{_pretty(left, in_tight=True)} . {_pretty(right, in_tight=True)}"
        case _:
            raise TypeError(f"unknown AST node: {type(node).__name__}")


# ---------------------------------------------------------------------------
# Equation grammar parser
# ---------------------------------------------------------------------------

_KEYWORDS = frozenset({"rec", "end"})


def parse_program(source: str) -> Program:
    """Parse a session type program (equation grammar).

    Supports three surface forms, all lowering to the same Program:
    - Bare expression: ``"&{a: end}"`` → ``Program(_main = &{a: end})``
    - Definition list: ``"S = &{a: T}\\nT = end"`` (newline-separated) or
      ``"S = &{a: T}, T = end"`` (comma-separated, ICE 2026 canonical)
    - Bare-main-plus-equations (ICE 2026 canonical):
      ``"S, X = &{a: end}, Y = +{b: end}"`` → Program with the main
      expression as ``_main`` plus named equations.

    Comma and newline separators are interchangeable; mixing them in the
    same source is permitted.

    Raises ``ParseError`` on invalid syntax.
    """
    tokens = tokenize(source)

    # Decide mode: if first two tokens are IDENT EQUALS, parse as definitions.
    # But skip if the ident is a keyword (rec, end).
    is_equation = (
        len(tokens) >= 3
        and tokens[0].kind is TokenKind.IDENT
        and tokens[0].value not in _KEYWORDS
        and tokens[1].kind is TokenKind.EQUALS
    )

    if is_equation:
        program = _parse_definitions(tokens)
        for defn in program.definitions:
            _enforce_wellformed_new(defn.body)
        return program

    # Bare expression — but the ICE 2026 canonical form allows
    #   ``S, X₁ = S₁, …, Xₙ = Sₙ``
    # where the head expression S is followed by comma-separated equations.
    # Parse the head first; if a top-level comma follows, continue with
    # _parse_definitions on the remainder.
    p = _Parser(tokens)
    main = p._par_expr()
    consumed = p._pos
    rest = tokens[consumed:]

    # Skip a single optional separator (comma) between main and equations.
    if rest and rest[0].kind is TokenKind.COMMA:
        rest = rest[1:]

    # If anything remains other than EOF, it must be equation definitions.
    if rest and rest[0].kind is not TokenKind.EOF:
        # Re-attach a sentinel EOF (the slice already includes one if tokens did).
        defs_program = _parse_definitions(rest)
        # Merge: _main first, then named equations.
        _enforce_wellformed_new(main)
        for defn in defs_program.definitions:
            _enforce_wellformed_new(defn.body)
        return Program(
            definitions=(Definition("_main", main),) + defs_program.definitions
        )

    # Plain bare expression — wrap as _main.
    _enforce_wellformed_new(main)
    return Program(definitions=(Definition("_main", main),))


def _parse_definitions(tokens: list[Token]) -> Program:
    """Parse a sequence of ``Name = S`` definitions from a token list."""
    definitions: list[Definition] = []
    pos = 0

    while pos < len(tokens) and tokens[pos].kind is not TokenKind.EOF:
        # Permit a comma separator between definitions (ICE 2026 canonical).
        # Newlines are absent from the token stream (the lexer skips them);
        # the original implementation relied on the next IDENT EQUALS pattern
        # to mark a new definition. We additionally accept an explicit
        # comma at this position.
        if tokens[pos].kind is TokenKind.COMMA:
            pos += 1
            if pos >= len(tokens) or tokens[pos].kind is TokenKind.EOF:
                raise ParseError(
                    "trailing comma after last definition", tokens[pos - 1].pos
                )

        # Expect: IDENT EQUALS body
        name_tok = tokens[pos]
        if name_tok.kind is not TokenKind.IDENT:
            raise ParseError(
                f"expected definition name, got {name_tok.kind.name} ({name_tok.value!r})",
                name_tok.pos,
            )
        if name_tok.value in _KEYWORDS:
            raise ParseError(
                f"{name_tok.value!r} is a keyword, not a valid definition name",
                name_tok.pos,
            )
        pos += 1

        eq_tok = tokens[pos]
        if eq_tok.kind is not TokenKind.EQUALS:
            raise ParseError(
                f"expected '=' after definition name {name_tok.value!r}, "
                f"got {eq_tok.kind.name} ({eq_tok.value!r})",
                eq_tok.pos,
            )
        pos += 1

        # Parse the body using _Parser starting at pos.
        # We need to find where this definition's body ends.
        # A definition body ends at: EOF, or the next IDENT EQUALS pattern
        # (where IDENT is not a keyword).
        # Strategy: feed remaining tokens to _Parser, let it parse one
        # _par_expr, then check how far it got.
        sub_tokens = tokens[pos:]
        p = _Parser(sub_tokens)
        body = p._par_expr()

        # How many tokens did the sub-parser consume?
        consumed = p._pos
        pos += consumed

        definitions.append(Definition(name_tok.value, body))

    if not definitions:
        raise ParseError("empty program: expected at least one definition", 0)

    return Program(definitions=tuple(definitions))


def pretty_program(program: Program) -> str:
    """Render a ``Program`` back to equation syntax.

    Single ``_main`` definitions are rendered as bare expressions.
    """
    if (
        len(program.definitions) == 1
        and program.definitions[0].name == "_main"
    ):
        return pretty(program.definitions[0].body)

    lines: list[str] = []
    for defn in program.definitions:
        lines.append(f"{defn.name} = {pretty(defn.body)}")
    return "\n".join(lines)
