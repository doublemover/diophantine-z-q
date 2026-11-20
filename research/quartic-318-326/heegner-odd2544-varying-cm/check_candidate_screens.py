#!/usr/bin/env python3
"""Verify just the known-support screens. Optional exact original W replay."""
import ast
import contextlib
import importlib.util
import io
import math
import pathlib
import sys

H = 473592745039516333133760
A = 500907037962860804880
BETA = (5, 11, 17, 163, 661, 733, 1489, 1861)
THETA_KNOWN = (131, 6551, 2470991, 16782959)
ROWS = (
    (521879, 199848, 90460, 118553),
    (977831, 237678, 679949, 273442),
)

def isprime(p):
    return p > 1 and all(p % i for i in range(2, math.isqrt(p) + 1))

def delta(p, w):
    return (1 - A * pow(w * pow(A + 1, -1, p), 2, p) * pow(17, -1, p)) % p

def original_rows(source):
    select = source / "select_scalar_specialization.py"
    spec = importlib.util.spec_from_file_location("select_scalar_specialization", select)
    circuit = importlib.util.module_from_spec(spec)
    with contextlib.redirect_stdout(io.StringIO()):
        spec.loader.exec_module(circuit)
    assert (circuit.h, circuit.A) == (H, A)
    pp = source / "check_actual_scalar_modular.py"
    tree = ast.parse(pp.read_text())
    wanted = {"parent_poly", "chartmod", "residue"}
    tree.body = [
        node for node in tree.body
        if isinstance(node, ast.FunctionDef) and node.name in wanted
    ]
    assert {node.name for node in tree.body} == wanted
    env = {"C": circuit}
    exec(compile(tree, str(pp), "exec"), env)
    for p, w, d, _ in ROWS:
        result = env["residue"](p)
        assert (result["W"], result["delta"]) == (w, d)

def main():
    assert all(isprime(p) for p in BETA + THETA_KNOWN + (53,))
    assert math.prod(THETA_KNOWN) % 24 == 13
    assert delta(53, 1) == 17 == 21**2 % 53
    for m, w, d, root in ROWS:
        assert isprime(m) and m % 24 == 23
        assert pow(-m, 26, 53) == 52
        assert all(pow(-m, (q - 1) // 2, q) == 1 for q in BETA + THETA_KNOWN)
        assert delta(m, w) == d == root**2 % m
    if len(sys.argv) == 2:
        original_rows(pathlib.Path(sys.argv[1]).resolve())
    print("Two necessary-only screens verified; no complete support or linked input.")

if __name__ == "__main__":
    main()
