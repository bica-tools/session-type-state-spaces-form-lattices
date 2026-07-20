"""reticulate — lattice analysis of session-type state spaces (v1.0.1)."""

from .parser import (
    parse,
    parse_program,
    pretty,
    ParseError,
    SessionType,
    End,
    Var,
    Branch,
    Select,
    Parallel,
    Rec,
    Definition,
    Program,
)
from .statespace import (
    build_statespace,
    build_statespace_from_program,
    StateSpace,
    Polarity,
)
from .lattice import (
    check_lattice,
    LatticeResult,
    compute_meet,
    compute_join,
    check_distributive,
    DistributivityResult,
)
from .termination import (
    is_terminating,
    check_termination,
    check_wf_parallel,
    TerminationResult,
    WFParallelResult,
)
from .product import (
    product_statespace,
    sync_product_statespace,
    sync_product_n,
    power_statespace,
    power_type,
)
from .resolve import (
    resolve,
    ResolveError,
)
from .visualize import (
    dot_source,
    hasse_diagram,
    render_hasse,
)

__version__ = '1.0.1'

__all__ = [
    'parse',
    'parse_program',
    'pretty',
    'ParseError',
    'SessionType',
    'End',
    'Var',
    'Branch',
    'Select',
    'Parallel',
    'Rec',
    'Definition',
    'Program',
    'build_statespace',
    'build_statespace_from_program',
    'StateSpace',
    'Polarity',
    'check_lattice',
    'LatticeResult',
    'compute_meet',
    'compute_join',
    'check_distributive',
    'DistributivityResult',
    'is_terminating',
    'check_termination',
    'check_wf_parallel',
    'TerminationResult',
    'WFParallelResult',
    'product_statespace',
    'sync_product_statespace',
    'sync_product_n',
    'power_statespace',
    'power_type',
    'resolve',
    'ResolveError',
    'dot_source',
    'hasse_diagram',
    'render_hasse',
]
