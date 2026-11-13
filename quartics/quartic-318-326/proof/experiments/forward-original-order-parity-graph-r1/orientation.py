"""Exact positive-modulus CRT/orientation solver. Standard library, no factoring.

Input orders are *supplied*, not produced. In the original application they must
be the two actual quotient orders of R at every one of the fifteen positions.
Node side 0 is minus (residue 0), side 1 is plus (residue 1).
"""
from collections import deque
from itertools import product
from math import gcd, lcm


def merge_crt(a, m, b, n):
    """Return the least residue and period, or None for incompatible congruences."""
    if m <= 0 or n <= 0:
        raise ValueError("CRT moduli must be positive")
    g = gcd(m, n)
    if (b - a) % g:
        return None
    modulus = n // g
    t = 0 if modulus == 1 else ((b - a) // g * pow(m // g, -1, modulus)) % modulus
    period = m * modulus
    return ((a + m * t) % period, period)


def exact_crt(Pi, minus, plus, L, h0):
    """The literal three residues, without the old gcd(plus,L)=1 restriction."""
    if min(Pi, minus, plus, L) <= 0 or h0 < 0:
        raise ValueError("positive moduli and nonnegative continuity residue required")
    A = Pi**3 * minus
    criterion = gcd(A, plus) == 1 and h0 % gcd(A, L) == 0 and (h0 - 1) % gcd(plus, L) == 0
    first = merge_crt(0, A, 1, plus)
    result = None if first is None else merge_crt(*first, h0, L)
    assert criterion == (result is not None)
    if result is not None:
        h, period = result
        assert h % A == 0 and (h - 1) % plus == 0 and (h - h0) % L == 0
        assert period == lcm(A, plus, L)
    return result


def moduli(pairs, orientation):
    if len(pairs) != len(orientation):
        raise ValueError("one orientation bit per position required")
    return (lcm(*(pair[s] for pair, s in zip(pairs, orientation))),
            lcm(*(pair[1 - s] for pair, s in zip(pairs, orientation))))


def compatible(pairs, orientation, Pi, L, h0):
    minus, plus = moduli(pairs, orientation)
    return exact_crt(Pi, minus, plus, L, h0) is not None


def solve(pairs, Pi, L, h0):
    """Return a compressed, exact family of orientations or a contradiction.

    The graph uses opposite-side partner edges and same-side nontrivial-gcd
    edges. The latter include within-position overlaps. Unary restrictions
    encode all remaining CRT tests. No primality factorization is used.
    """
    if not pairs or any(len(pair) != 2 for pair in pairs):
        raise ValueError("a nonempty family of pairs is required")
    if min(Pi, L, *(n for pair in pairs for n in pair)) <= 0 or h0 < 0:
        raise ValueError("positive orders/moduli and nonnegative h0 required")
    values = [n for pair in pairs for n in pair]
    count = len(values)
    graph = [[] for _ in values]
    edges = []

    def edge(u, v, parity, reason):
        edges.append([u, v, parity, reason])
        graph[u].append((v, parity))
        graph[v].append((u, parity))

    for i in range(len(pairs)):
        edge(2*i, 2*i+1, 1, "opposite members of the same position")
    for u in range(count):
        for v in range(u+1, count):
            g = gcd(values[u], values[v])
            if g > 1:
                edge(u, v, 0, f"common divisor {g}")
    colors = [None] * count
    component = [None] * count
    components = []
    for root in range(count):
        if colors[root] is not None:
            continue
        cid = len(components)
        nodes = []
        colors[root] = 0
        component[root] = cid
        queue = deque([root])
        while queue:
            u = queue.popleft()
            nodes.append(u)
            for v, parity in graph[u]:
                expected = colors[u] ^ parity
                if colors[v] is None:
                    colors[v] = expected
                    component[v] = cid
                    queue.append(v)
                elif colors[v] != expected:
                    return {"satisfiable": False, "reason": "inconsistent parity graph", "conflicting_edge": [u, v, parity], "edges": edges}
        components.append(nodes)
    allowed = []
    forced = {}
    forced_by = {}
    for u, n in enumerate(values):
        choices = []
        if h0 % gcd(Pi**3*n, L) == 0:
            choices.append(0)
        if gcd(Pi, n) == 1 and (h0-1) % gcd(n, L) == 0:
            choices.append(1)
        allowed.append(choices)
        if not choices:
            return {"satisfiable": False, "reason": "order has no allowed side", "node": u, "value": n}
        if len(choices) == 1:
            cid = component[u]
            required = choices[0] ^ colors[u]
            if cid in forced and forced[cid] != required:
                return {"satisfiable": False, "reason": "inconsistent forced component", "nodes": [forced_by[cid], u]}
            forced[cid] = required
            forced_by[cid] = u
    free = [cid for cid in range(len(components)) if cid not in forced]
    return {"satisfiable": True, "positions": len(pairs), "edges": edges,
            "components": components, "colors": colors, "component_of": component,
            "allowed_sides": allowed, "forced_components": forced,
            "free_components": free, "orientation_count": 2**len(free)}


def orientations(solution):
    """Expand only when the caller wants the individual root assignments."""
    if not solution["satisfiable"]:
        return
    for bits in product((0, 1), repeat=len(solution["free_components"])):
        choices = dict(solution["forced_components"])
        choices.update(zip(solution["free_components"], bits))
        yield tuple(solution["colors"][2*i] ^ choices[solution["component_of"][2*i]] for i in range(solution["positions"]))
