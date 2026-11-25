"""Universal native embedding identities with NONCOMMUTING coefficients.

An exact free associative algebra over rationals with odd denominators.
Monomial order is retained. Thus these identities also apply when the
coefficients are context operators, whose product is composition.
"""
from dataclasses import dataclass
from fractions import Fraction
import inverse_limit_microcosm as native


@dataclass(frozen=True, eq=False)
class Polynomial:
    terms: tuple

    @staticmethod
    def make(terms):
        out = {}
        for word, coefficient in terms:
            word, coefficient = tuple(word), Fraction(coefficient)
            out[word] = out.get(word, Fraction(0)) + coefficient
        return Polynomial(tuple(sorted((w, c) for w, c in out.items() if c)))

    @staticmethod
    def cast(value):
        return value if isinstance(value, Polynomial) else Polynomial.make([((), value)])

    @staticmethod
    def variable(name):
        return Polynomial.make([((name,), 1)])

    def __add__(self, other):
        return Polynomial.make(self.terms + Polynomial.cast(other).terms)

    def __radd__(self, other):
        return self + other

    def __neg__(self):
        return Polynomial.make((w, -c) for w, c in self.terms)

    def __sub__(self, other):
        return self + -Polynomial.cast(other)

    def __rsub__(self, other):
        return Polynomial.cast(other) + -self

    def __mul__(self, other):
        other = Polynomial.cast(other)
        # Concatenation, rather than sorting, is the critical point.
        return Polynomial.make((w + v, c * d)
                               for w, c in self.terms for v, d in other.terms)

    def __rmul__(self, other):
        return Polynomial.cast(other) * self

    def __eq__(self, other):
        return self.terms == Polynomial.cast(other).terms


def flatten(value):
    if isinstance(value, (tuple, list)):
        for x in value:
            yield from flatten(x)
    else:
        yield Polynomial.cast(value)


def identity(name, left, right):
    a, b = list(flatten(left)), list(flatten(right))
    if len(a) != len(b) or any(x != y for x, y in zip(a, b)):
        raise ValueError('noncommutative identity failed: ' + name)
    if any(c.denominator % 2 == 0 for p in a + b for _, c in p.terms):
        raise ValueError('nonintegral dyadic denominator')
    return {'identity': name, 'components': len(a),
            'method': 'Exact normalization in the free ASSOCIATIVE algebra; word order retained'}


def certificate():
    a = tuple(Polynomial.variable('a' + str(i)) for i in range(6))
    b = tuple(Polynomial.variable('b' + str(i)) for i in range(6))
    c = tuple(Polynomial.variable('c' + str(i)) for i in range(6))
    image = native.rho(a)
    decoded = image[3][3], image[3][0], image[1][1], image[1][2], image[2][1], image[2][2]
    proofs = [
        identity('delta rho = id for arbitrary noncommuting coefficients', decoded, a),
        identity('rho(ab) = rho(a)rho(b) for arbitrary noncommuting coefficients',
                 native.rho(native.native_product(a, b)), native.mm(native.rho(a), native.rho(b))),
        identity('Associativity of the native coordinate product over operator coefficients',
                 native.native_product(native.native_product(a, b), c),
                 native.native_product(a, native.native_product(b, c))),
    ]
    import torsor_matrix as frames
    aa = {g: Polynomial.variable('u_' + g) for g in frames.NAMES}
    bb = {g: Polynomial.variable('v_' + g) for g in frames.NAMES}
    coordinates = lambda coefficients: tuple(
        sum(coefficients[g] * frames.ELEMENTS[g][i] for g in frames.NAMES)
        for i in range(6))
    convolution = {k: sum(aa[g] * bb[h] for g in frames.NAMES for h in frames.NAMES
                          if frames.multiply(g, h) == k) for k in frames.NAMES}
    proofs.append(identity('S3 group-ring convolution equals the native coordinate product over noncommuting coefficients',
                           native.native_product(coordinates(aa), coordinates(bb)),
                           coordinates(convolution)))
    # Exact determinant of the six coordinate columns. An odd determinant is
    # a unit in every Z_(2)-algebra, so this is a universal invertible change
    # of six coefficient coordinates, not a commutativity assumption on R.
    columns = [[Fraction(frames.ELEMENTS[g][i]) for g in frames.NAMES] for i in range(6)]
    determinant = Fraction(1)
    for i in range(6):
        pivot = next(j for j in range(i, 6) if columns[j][i])
        if pivot != i:
            columns[i], columns[pivot] = columns[pivot], columns[i]
            determinant = -determinant
        value = columns[i][i]
        determinant *= value
        for j in range(i + 1, 6):
            ratio = columns[j][i] / value
            columns[j] = [x - ratio * y for x, y in zip(columns[j], columns[i])]
    if abs(determinant) != 27:
        raise ValueError('native S3 basis determinant failed')
    x, y = Polynomial.variable('x'), Polynomial.variable('y')
    if x * y == y * x:
        raise ValueError('the verification algebra accidentally became commutative')
    return {'coefficient_domain': 'Any associative algebra over Z_(2), including context-operator algebras',
            'proofs': proofs,
            'native_group_basis_determinant': str(determinant),
            'source_operations_enumerated': 0,
            'scope': 'Faithful multiplicative native 4x4 embedding; no universal scalar-cost claim'}
