"""Sparse rational polynomials keyed by (coordinate multiset, S exponent)."""

from fractions import Fraction as Q
from collections import defaultdict
from hashlib import sha256
import json


def digest(p):
    return sha256(p.read_bytes()).hexdigest()


def read(p):
    return json.loads(p.read_text(encoding="utf-8-sig"))


def clean(p):
    return {k: v for k, v in p.items() if v}


def poly(terms):
    p = defaultdict(Q)
    for t in terms:
        mon = tuple(t["monomial"])
        s = t.get("sPower", 0)
        assert tuple(sorted(mon)) == mon and isinstance(s, int) and s >= 0
        p[mon, s] += Q(t["coefficient"])
    return clean(p)


def add(p, q):
    r = defaultdict(Q, p)
    for k, v in q.items():
        r[k] += v
    return clean(r)


def mul(p, q):
    r = defaultdict(Q)
    for (m, s), a in p.items():
        for (n, t), b in q.items():
            r[tuple(sorted(m + n)), s + t] += a * b
    return clean(r)


def subst(p, images):
    r = {}
    for (m, s), a in p.items():
        term = {((), s): a}
        for v in m:
            term = mul(term, images.get(v, {((v,), 0): Q(1)}))
        r = add(r, term)
    return r


def rows(d):
    out = {r["id"]: poly(r["terms"]) for r in d["residuals"]}
    assert len(out) == len(d["residuals"])
    return out
