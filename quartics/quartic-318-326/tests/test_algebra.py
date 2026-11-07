from fractions import Fraction
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import compile as compiler
from sparse import add, mul, poly, subst


class SparsePolynomialTests(unittest.TestCase):
    def test_duplicate_terms_cancel(self):
        self.assertEqual(
            poly(
                [
                    {"monomial": [1], "sPower": 2, "coefficient": "1/3"},
                    {"monomial": [1], "sPower": 2, "coefficient": "-1/3"},
                ]
            ),
            {},
        )

    def test_multiplication_keeps_parameter_and_coordinate_degrees_separate(self):
        self.assertEqual(
            mul({((2,), 3): Fraction(1, 2)}, {((1,), 4): Fraction(2, 3)}),
            {((1, 2), 7): Fraction(1, 3)},
        )

    def test_affine_shear_is_invertible_for_quadratic_rows(self):
        forward = {
            1: {((1,), 0): Fraction(1), ((2,), 1): Fraction(-1)},
            2: {((2,), 0): Fraction(1, 4096)},
        }
        inverse = {
            1: {((1,), 0): Fraction(1), ((2,), 1): Fraction(4096)},
            2: {((2,), 0): Fraction(4096)},
        }
        row = {
            ((1, 2), 0): Fraction(3),
            ((2, 2), 1): Fraction(-2),
            ((), 0): Fraction(5),
        }
        self.assertEqual(subst(subst(row, forward), inverse), row)

    def test_zero_polynomial_stays_zero(self):
        self.assertEqual(mul({}, {((0,), 0): Fraction(1)}), {})
        self.assertEqual(add({((0,), 0): Fraction(1)}, {((0,), 0): Fraction(-1)}), {})


class CompilerTests(unittest.TestCase):
    def test_elimination_and_degree_constraints(self):
        compiler.self_test()


if __name__ == "__main__":
    unittest.main()
