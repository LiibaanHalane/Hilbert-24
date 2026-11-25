#!/usr/bin/env python3
"""Canonical source codec, Collatz cylinders and six-frame incidence carrier.

No SAT algorithm is defined here. The native source compiler imports these
exact arithmetic charts before executing any source operation.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, field
from fractions import Fraction
import json
from pathlib import Path
from typing import Iterable, Sequence


def gamma(value: int) -> tuple[int, ...]:
    """Self-delimiting code of a natural number, including zero."""
    if type(value) is not int or value < 0:
        raise ValueError("a natural number is required")
    bits = tuple(map(int, bin(value + 1)[2:]))
    return (0,) * (len(bits) - 1) + bits


class Reader:
    def __init__(self, bits: Sequence[int]):
        self.bits, self.offset = bits, 0

    def bit(self) -> int:
        if self.offset >= len(self.bits):
            raise ValueError("truncated canonical word")
        value = self.bits[self.offset]
        self.offset += 1
        if value not in (0, 1):
            raise ValueError("non-binary digit")
        return value

    def natural(self) -> int:
        zeroes = 0
        while self.bit() == 0:
            zeroes += 1
        value = 1
        for _ in range(zeroes):
            value = 2 * value + self.bit()
        return value - 1


def signed_code(literal: int) -> int:
    return 2 * (abs(literal) - 1) + (literal < 0)


def signed_decode(value: int) -> int:
    return -(value // 2 + 1) if value & 1 else value // 2 + 1


@dataclass(frozen=True)
class Source:
    n: int
    clauses: tuple[tuple[int, ...], ...]

    def __post_init__(self):
        if type(self.n) is not int or self.n < 0:
            raise ValueError("invalid source arity")
        object.__setattr__(self, "clauses", tuple(tuple(c) for c in self.clauses))
        for clause in self.clauses:
            for literal in clause:
                if type(literal) is not int or literal == 0 or abs(literal) > self.n:
                    raise ValueError("literal outside the original source signature")

    def as_dict(self) -> dict:
        return {"n": self.n, "clauses": [list(c) for c in self.clauses]}

    def word(self) -> tuple[int, ...]:
        bits = list(SOURCE_MAGIC + gamma(self.n) + gamma(len(self.clauses)))
        for clause in self.clauses:
            bits.extend(gamma(len(clause)))
            for literal in clause:
                bits.extend(gamma(signed_code(literal)))
        return tuple(bits)

    @classmethod
    def parse(cls, reader: Reader) -> Source:
        if tuple(reader.bit() for _ in SOURCE_MAGIC) != SOURCE_MAGIC:
            raise ValueError("wrong canonical source tag")
        n, count = reader.natural(), reader.natural()
        clauses = []
        for _ in range(count):
            clauses.append(tuple(signed_decode(reader.natural())
                                 for _ in range(reader.natural())))
        return cls(n, tuple(clauses))


SOURCE_MAGIC = (1, 0, 1, 0, 0, 1)


def inverse_odd_power_two(value: int, bits: int) -> int:
    """Exact inverse by doubling proved 2-adic precision, with no cutoff."""
    if type(bits) is not int or bits < 0 or type(value) is not int or not value & 1:
        raise ValueError("an odd integer and a natural precision are required")
    if not bits:
        return 0
    inverse, precision = 1, 1
    while precision < bits:
        precision = min(2*precision,bits)
        mask = (1 << precision)-1
        inverse = (inverse*(2-(value & mask)*inverse)) & mask
    return inverse


@dataclass(frozen=True)
class Ball:
    """C_w=B_k(r), with an arbitrary, uninspected infinite tail."""
    word: tuple[int, ...]
    residue: int
    odd_steps: int
    offset: int

    @classmethod
    def from_word(cls, word: Iterable[int]) -> Ball:
        word = tuple(word)
        h = c = 0
        for j, bit in enumerate(word):
            if bit not in (0, 1):
                raise ValueError("non-binary instruction")
            if bit:
                c = 3*c+(1 << j)
                h += 1
        modulus = 1 << len(word)
        residue = (-c * inverse_odd_power_two(3 ** h,len(word))) & (modulus-1) if word else 0
        return cls(word, residue, h, c)

    @classmethod
    def from_godel(cls, number: int) -> Ball:
        if type(number) is not int or number < 0:
            raise ValueError("invalid basis-ball number")
        k = (number + 1).bit_length() - 1
        a = number - ((1 << k) - 1)
        current, word = a, []
        for _ in range(k):
            bit = current & 1
            word.append(bit)
            current = (3*current+1) >> 1 if bit else current >> 1
        answer = cls.from_word(word)
        if answer.residue != a:
            raise ValueError("canonical decoder equation failed")
        return answer

    @property
    def depth(self) -> int:
        return len(self.word)

    @property
    def godel(self) -> int:
        return (1 << self.depth) - 1 + self.residue

    def all_tail(self, tail: Fraction) -> Fraction:
        """Rational instance of the all-tail identity; odd denominators only."""
        if tail.denominator % 2 == 0:
            raise ValueError("tail must be a 2-adic integral rational")
        return ((1 << self.depth) * tail - self.offset) / (3 ** self.odd_steps)

    def ancestor(self, depth: int) -> tuple[int, int]:
        if not 0 <= depth <= self.depth:
            raise ValueError("not an ancestor depth")
        r = self.residue % (1 << depth)
        return depth, (1 << depth) - 1 + r


def matmul(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return ((a[0]*b[0]+a[1]*b[2]) & 1, (a[0]*b[1]+a[1]*b[3]) & 1,
            (a[2]*b[0]+a[3]*b[2]) & 1, (a[2]*b[1]+a[3]*b[3]) & 1)


IDENTITY, ROTATION, REFLECTION = (1, 0, 0, 1), (0, 1, 1, 1), (0, 1, 1, 0)
ROTATION2 = matmul(ROTATION, ROTATION)
FRAMES = (IDENTITY, ROTATION, ROTATION2, REFLECTION,
          matmul(REFLECTION, ROTATION), matmul(REFLECTION, ROTATION2))


@dataclass(frozen=True)
class Position:
    evidence: int = 0
    question: int = 1

    def __post_init__(self):
        if self.evidence not in range(4) or self.question not in range(4):
            raise ValueError("outside the sixteen-position incidence carrier")

    @property
    def code(self) -> int:
        return self.evidence | (self.question << 2)

    def header(self) -> tuple[int, ...]:
        return tuple((self.code >> i) & 1 for i in range(4))

    def observe(self) -> tuple[tuple[int, int], ...]:
        b = self.header()
        return tuple((b[i], b[j]) for i, j in ((0,1),(2,3),(0,2),(1,2),(0,3),(1,3)))

    @property
    def supported(self) -> bool:
        return ((self.evidence & 1) * (self.question & 1)
                + (self.evidence >> 1) * (self.question >> 1)) % 2 == 1

    def reframe(self, frame: int) -> Position:
        a,b,c,d = FRAMES[frame]
        p,n = self.evidence & 1, self.evidence >> 1
        q,r = self.question & 1, self.question >> 1
        # g v, and q g^-1; determinant is one over F_2.
        return Position(((a*p+b*n)&1) | (((c*p+d*n)&1)<<1),
                        ((q*d+r*c)&1) | (((q*b+r*a)&1)<<1))


