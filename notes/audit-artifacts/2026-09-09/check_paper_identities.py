"""Exact checks of the paper's elementary identities in the LvdW coordinate model.

Source: Levi--van der Waerden (1933), printed p. 156, formula (9), inspected
from references/rendered-pages/levi-van-der-waerden-1933/. Coefficients are in
GF(3). This is a separate computational audit, not a Lean proof of the paper.
The source's normal-form theorem identifies the 14-coordinate rank-four model
with B(4, 3). Four arbitrary model elements are represented by 56 independent
polynomial indeterminates. A zero residual is an exact polynomial identity.

Run with Python 3 and SymPy; no floating point or randomized tests are used.
"""

import json
from itertools import combinations

import sympy
from sympy.polys.domains import GF
from sympy.polys.rings import ring


RANK = 4
KEYS = [(i,) for i in range(RANK)]
KEYS += list(combinations(range(RANK), 2))
KEYS += list(combinations(range(RANK), 3))
NAMES = [f"{letter}_{''.join(map(str, key))}" for letter in "abcd" for key in KEYS]
POLY_RING, *INDETERMINATES = ring(",".join(NAMES), GF(3))
ONE = {key: POLY_RING.zero for key in KEYS}


def mul(c, d):
    """Formula (9), in increasing generator/pair/triple coordinates."""
    e = {}
    for (i,) in combinations(range(RANK), 1):
        e[i,] = c[i,] + d[i,]
    for i, j in combinations(range(RANK), 2):
        e[i, j] = c[i, j] + d[i, j] - c[j,] * d[i,]
    for i, j, k in combinations(range(RANK), 3):
        e[i, j, k] = (
            c[i, j, k] + d[i, j, k]
            + c[i, j] * d[k,] - c[i, k] * d[j,]
            + (c[j, k] - c[j,] * c[k,] - c[j,] * d[k,] + c[k,] * d[j,]) * d[i,]
        )
    return e


def inv(c):
    # The exponent-three law is checked separately before using this formula.
    return mul(c, c)


def prod(*elements):
    result = ONE
    for element in elements:
        result = mul(result, element)
    return result


def comm(a, b):
    # Paper convention, TeX line 146.
    return prod(a, b, inv(a), inv(b))


def triple(a, b, c):
    return comm(comm(a, b), c)


def conj(a, g):
    # Paper a^g = g^{-1} a g.
    return prod(inv(g), a, g)


def assert_equal(name, left, right, results):
    residual = {str(key): str(left[key] - right[key]) for key in KEYS if left[key] != right[key]}
    assert not residual, (name, residual)
    results.append({"name": name, "zero_coordinate_residuals": len(KEYS)})


def main():
    elements = []
    for index in range(4):
        start = index * len(KEYS)
        elements.append(dict(zip(KEYS, INDETERMINATES[start:start + len(KEYS)])))
    a, b, c, d = elements
    results = []
    equal = lambda name, left, right: assert_equal(name, left, right, results)
    equal("coordinate law associative", mul(mul(a, b), c), mul(a, mul(b, c)))
    equal("coordinate law left identity", mul(ONE, a), a)
    equal("coordinate law right identity", mul(a, ONE), a)
    equal("coordinate law exponent three", prod(a, a, a), ONE)
    equal("fourfold commutator", comm(triple(a, b, c), d), ONE)
    equal("derived commutators commute", comm(comm(a, b), comm(c, d)), ONE)
    equal("triple cyclic", triple(a, b, c), triple(b, c, a))
    equal("two Engel", triple(a, b, b), ONE)
    equal("inverse right", comm(a, inv(b)), inv(comm(a, b)))
    equal("inverse left", comm(inv(a), b), inv(comm(a, b)))
    equal("conjugates of same element commute", comm(conj(a, b), conj(a, c)), ONE)
    equal("triple antisymmetric", triple(a, b, c), inv(triple(b, a, c)))
    equal("TeX 366 right multiplication", comm(a, mul(b, c)),
          prod(comm(a, b), comm(a, c), triple(a, b, c)))
    equal("TeX 367 left multiplication", comm(mul(a, b), c),
          prod(comm(a, c), comm(b, c), inv(triple(a, b, c))))
    equal("TeX 662 commutator compression", mul(comm(a, b), comm(a, c)),
          comm(a, prod(b, c, comm(b, c))))
    equal("TeX 663 conjugate expression", conj(a, b), mul(a, comm(a, b)))

    # These deliberately false versions ensure nonzero triple coordinates are
    # detected and the check is not accidentally taking a class-two quotient.
    assert triple(a, b, c) != ONE
    assert comm(a, mul(b, c)) != prod(comm(a, b), comm(a, c), inv(triple(a, b, c)))
    assert comm(mul(a, b), c) != prod(comm(a, c), comm(b, c), triple(a, b, c))
    print(json.dumps({
        "sympy_version": sympy.__version__,
        "coefficient_field": "GF(3)",
        "free_rank": RANK,
        "coordinate_count": len(KEYS),
        "generic_element_count": 4,
        "polynomial_indeterminate_count": len(INDETERMINATES),
        "checks": results,
        "negative_controls": "nonzero triple and both incorrect product signs detected",
        "scope": "elementary identities only; not the coproduct or model-companion proof",
    }, indent=2))


if __name__ == "__main__":
    main()
