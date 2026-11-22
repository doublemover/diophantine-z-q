"""Check the exact raw row and fill bytes, then normalize all 15 rows over Q."""
import argparse
import ast
from fractions import Fraction as F
from hashlib import sha256
from pathlib import Path
import re


class P(dict):
    """Finite rational polynomial; keys are sorted tuples of variables."""

    @staticmethod
    def c(x):
        return x if isinstance(x, P) else P({(): F(x)} if x else {})

    def __add__(self, other):
        a = P(self)
        for m, v in P.c(other).items():
            a[m] = a.get(m, F(0)) + v
            if not a[m]:
                del a[m]
        return a

    def __neg__(self):
        return P({m: -v for m, v in self.items()})

    def __sub__(self, other):
        return self + -P.c(other)

    def __mul__(self, other):
        a = P()
        for m, v in self.items():
            for n, w in P.c(other).items():
                i = tuple(sorted(m + n))
                a[i] = a.get(i, F(0)) + v * w
                if not a[i]:
                    del a[i]
        return a

    def __pow__(self, n):
        assert type(n) is int and n >= 0
        a = P.c(1)
        for _ in range(n):
            a = a * self
        return a

    def subst(self, replacements):
        result = P()
        for m, v in self.items():
            term = P.c(v)
            for n in m:
                term = term * replacements.get(n, P({(n,): F(1)}))
            result = result + term
        return result


def parse(s, syms):
    def visit(node):
        if isinstance(node, ast.Expression):
            return visit(node.body)
        if isinstance(node, ast.Constant) and type(node.value) is int:
            return P.c(node.value)
        if isinstance(node, ast.Name):
            return syms[node.id]
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
            return -visit(node.operand)
        if isinstance(node, ast.BinOp):
            a, b = visit(node.left), visit(node.right)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Sub):
                return a - b
            if isinstance(node.op, ast.Mult):
                return a * b
            if isinstance(node.op, ast.Div) and set(b) == {()}:
                return a * P.c(1 / b[()])
        raise ValueError(ast.dump(node))

    return visit(ast.parse(s, mode="eval"))


def exact_bytes(path, digest):
    raw = path.read_bytes()
    assert sha256(raw).hexdigest() == digest, path.name
    return raw.decode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("raw", type=Path, help="exact Raw318FinalReplayData.lean")
    parser.add_argument("fill", type=Path, help="exact ThreePoleCertificates318.lean")
    args = parser.parse_args()
    raw = exact_bytes(args.raw, "c563f76c563192a218c3bdf22714ab73f36d3a0ed9c629a346d7d3bb9fa80457")
    fill = exact_bytes(args.fill, "e751b9e9f9125245a152f9cb1d9cb28e3a48571e1de09b101390d851eb85cab8")
    named = {n: P({(n,): F(1)}) for n in ("b", "e", "s", "p", "q", "z1", "z2", "z3")}
    b, e, s, p, q, z1, z2, z3 = named.values()
    C = P.c
    G = (s**2 - e * (C(17) - b)) * (s**2 + C(3) * e * (C(17) - b))
    expected = (
        z1 - e*b,
        z2 - s**2,
        C(3)*e*z1 + C(17)*p**2 - C(289)*b - C(34)*z1,
        z3 - (C(17)*e-z1)**2 + C(F(2,3))*(C(17)*e-z1)*z2 + C(F(1,3))*z2**2,
        C(17)*q**2 + C(3)*b*z3,
    )
    filled = {"z1": e*b, "z2": s**2, "z3": -G*C(F(1,3))}
    reduced = (C(0), C(0), C(17)*p**2-b*(C(17)-e)*(C(17)+C(3)*e), C(0), C(17)*q**2-b*G)
    for j, subscript in enumerate("₀₁₂"):
        pole = 190 + 51*j
        es, ss, ps, qs = (39 + 4*j + k for k in range(4))
        xs, ys, ws = (191 + 51*j + k for k in range(3))
        slots = dict(zip((pole,es,ss,ps,qs,xs,ys,ws),named))
        block = [f"if i={n} then C{subscript}.{v} else"
                 for n,v in zip((es,ss,ps,qs), "espq")]
        block += [f"if i={xs} then C{subscript}.e*w {pole} else",
                  f"if i={ys} then C{subscript}.s^2 else",
                  f"if i={ws} then -((C{subscript}.s^2-C{subscript}.e*(17-w {pole}))*(C{subscript}.s^2+3*(C{subscript}.e*(17-w {pole}))))/3 else"]
        assert "\n  ".join(block) in fill
        rows = list(range(152 + 53*j, 157 + 53*j))
        for i, rid in enumerate(rows):
            source = re.search(rf"def r{rid}\b[^\n]*:= (.*)", raw).group(1)
            expr = re.sub(r"w (\d+)",lambda m: slots[int(m[1])],source)
            c = parse(expr,named)
            assert c == expected[i] and c.subst(filled) == reduced[i], rid
        print(f"pole {pole}, slots {es},{ss},{ps},{qs}; {xs},{ys},{ws}: exact rows {rows}; first {rows[0]},{rows[2]}")
    print("15 raw polynomial identities and all three fill blocks passed")


if __name__ == "__main__":
    main()
