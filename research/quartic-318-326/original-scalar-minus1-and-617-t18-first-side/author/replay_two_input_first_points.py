from fractions import Fraction
import json

def inputR(a):
    x = a + a*a
    f = x*x + Fraction(496408687, 100291113)*x**3 + Fraction(197130368, 33430371)*x**4
    return 101783690143177584*x + 267108917866935984*x*x + 533801448346128768*f + 4376874610839020

betas = (204618888056724185, 199477972060937362209233596181078921)
rs = (4376874610839020, 66540735456245258815946020283188225080332)
rows = {}
assert inputR(0) == inputR(-1) == rs[0]
for a, beta, R, m in zip((-1, 617), betas, rs, (1, 11*359)):
    assert inputR(a) == R and R % 4 == 0
    B0 = 187*R//4
    K = 1 + 114444*R
    assert B0 == m*m*beta and K == 1 + 2448*B0
    assert 17*114444*R == beta*(204*m)**2
    t = 18
    nu = beta*t*t
    A = 1+3*nu
    k = (1-nu)*(1-9*nu)
    n = beta*k
    X = beta*A*A
    Y = 8*beta**2*t*A*(1-3*nu)
    assert A*A-k == 16*nu and 0 < k < A*A and Y != 0
    assert X-n == (4*beta*t)**2 and X+3*n == 4*beta*(1-3*nu)**2
    assert Y*Y == X*(X-n)*(X+3*n)
    rows[str(a)] = dict(R=R, B0=B0, beta=beta, rho_multiplier=204*m, K=K,
                        n=n, n_mod_169=n%169, x=X, y=Y)
assert rows['-1']['n'] == 8094120968054829661910126903116889587959583856144085429185
assert rows['-1']['n_mod_169'] == 80 and rows['617']['n_mod_169'] == 13
assert betas[0] % 25 == 10 and betas[1] % 5 == 1
print(json.dumps(dict(scope='fixed integers, first equations only; no evaluated scalar or complement', rows=rows), indent=2, sort_keys=True))
