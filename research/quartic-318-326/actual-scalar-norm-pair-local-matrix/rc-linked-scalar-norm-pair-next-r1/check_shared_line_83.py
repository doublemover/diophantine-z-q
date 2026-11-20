"""Exact finite adjunct to the odd-discriminant tangent argument."""
import json
from pathlib import Path

here = Path(__file__).resolve().parent
src = here.parent / 'rc-linked-scalar-norm-pair-r1' / 'ACTUAL-ALT-PRIME-83.json'
j = json.loads(src.read_text())
p = 83
B = 204618888056724185
c = j['c']
assert j['prime'] == p and ((49*B*c*c - 48) % (p*p)) == 81*p
rho = 12*pow(7*c, -1, p) % p
rho = (rho - ((rho*rho - 3*B)//p)*pow(2*rho, -1, p)*p) % (p*p)
eps = (7*rho*c - 12) % (p*p)
assert (rho*rho - 3*B) % (p*p) == 0 and eps == 62*p
chi = lambda x: pow(x % p, (p-1)//2, p)
assert chi(-3*B) == p-1
count = 0
bad = []
for x in range(p):
    X2, Y2 = (x+c) % p, (1+B*c*x) % p
    Us = [u for u in range(p) if (u*u - 4 + 3*B*x*x) % p == 0]
    Vs = [v for v in range(p) if (v*v - 4*Y2*Y2 + 3*B*X2*X2) % p == 0]
    assert (7*(2*Y2-rho*X2) - (2+rho*x)) % p == 0
    for U in Us:
        for V in Vs:
            # All sign flips preserve the tangent-ratio class, since 3B is square.
            d = (2-U) % p or (2+U) % p
            n = (2*Y2-V) % p or (2*Y2+V) % p
            assert d and n
            if chi(7*n*pow(d, -1, p)) != 1:
                bad.append([x,U,V])
            count += 1
assert bad == [[14,0,0]]
print(json.dumps(dict(prime=p,rho_mod_p2=rho,epsilon_mod_p2=eps,
    affine_residue_triples=count,all_nonsquare_tangent_ratio_cases=bad),indent=2))
