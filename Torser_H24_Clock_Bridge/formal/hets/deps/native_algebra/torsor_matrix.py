"""The literal six-frame bitorsor and its native four-by-four matrix blocks.

Arbitrary context operations are represented by sparse indexed columns.
Evaluating a column evaluates its supplied source operation; this module
does not turn evaluation into a free or constant-time instruction.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Hashable
import inverse_limit_microcosm as native


NAMES = ('e', 'r', 'rr', 's', 'sr', 'srr')
E = (1, 0, 1, 0, 0, 1)
R = (1, 0, 0, -1, 1, -1)
S = (1, 1, 0, 1, 1, 0)
RR = native.native_product(R, R)
ELEMENTS = dict(zip(NAMES, (E, R, RR, S,
                          native.native_product(S, R),
                          native.native_product(S, RR))))
MATRICES = {g: native.rho(a) for g, a in ELEMENTS.items()}


def multiply(g: str, h: str) -> str:
    result = native.native_product(ELEMENTS[g], ELEMENTS[h])
    return next(k for k in NAMES if ELEMENTS[k] == result)


def inverse(g: str) -> str:
    return next(h for h in NAMES if multiply(g, h) == multiply(h, g) == 'e')


@dataclass(frozen=True)
class Operation:
    target: Callable[[Hashable], Hashable]
    frame: Callable[[Hashable], str]

    def column(self, x):
        return self.target(x), MATRICES[self.frame(x)]

    def after(self, first: Operation) -> Operation:
        return Operation(lambda x: self.target(first.target(x)),
                         lambda x: multiply(self.frame(first.target(x)), first.frame(x)))

    def dense(self, inputs, outputs):
        """Materialize only a declared finite demanded matrix, with 4x4 blocks."""
        inputs, outputs = tuple(inputs), tuple(outputs)
        rows = {y: i for i, y in enumerate(outputs)}
        if len(rows) != len(outputs):
            raise ValueError('output basis labels must be distinct')
        out = [[0] * (4 * len(inputs)) for _ in range(4 * len(outputs))]
        for j, x in enumerate(inputs):
            y, block = self.column(x)
            if y not in rows:
                raise ValueError('operation leaves the declared output basis')
            for a in range(4):
                for b in range(4):
                    out[4 * rows[y] + a][4 * j + b] = block[a][b]
        return tuple(map(tuple, out))


def certificate():
    # These are ALL pairs of the fixed finite frame algebra. The arbitrary-
    # index composition and faithfulness theorems are the Agda proofs.
    comparisons = []
    for g in NAMES:
        for h in NAMES:
            product = native.mm(MATRICES[g], MATRICES[h])
            if product != MATRICES[multiply(g, h)]:
                raise ValueError('native matrix/frame multiplication mismatch')
            comparisons.append([g, h, multiply(g, h)])
    residues = {tuple(tuple(v % 2 for v in row) for row in a)
                for a in MATRICES.values()}
    if len(residues) != 6:
        raise ValueError('frame representation is not faithful already modulo 2')
    # The diagonal t,b entries and middle block are a literal left inverse of
    # rho. This statement holds symbolically in polynomial_kernel as well.
    decoded = {g: native.delta(a, 8) for g, a in MATRICES.items()}
    return {
        'group': 'The existing supported S3 torsor, with basis e,r,rr,s,sr,srr',
        'matrix_rank_per_context': 4,
        'faithful_frame_images_modulo_2': len(residues),
        'complete_frame_product_table': comparisons,
        'native_matrices': MATRICES,
        'decoded_native_residues_modulo_256': decoded,
        'arbitrary_context_theorem': 'Agda IndexedTorsorOperations.matrix-composition and faithful-target/block',
        'source_operations_enumerated': 0,
        'scope': 'Native frame blocks plus arbitrary supplied context operations; no constant-size universal-matrix claim',
    }
