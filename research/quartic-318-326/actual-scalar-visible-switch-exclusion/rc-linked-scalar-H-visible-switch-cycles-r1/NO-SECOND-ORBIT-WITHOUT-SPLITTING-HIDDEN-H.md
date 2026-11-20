# Any new beta-norm orbit for the actual H must split its hidden part

Keep the exact fixed scalar \(H=Z^2-\beta C^2\) and the four
known pairwise distinct prime divisors \(V=131\cdot6551\cdot
2470991\cdot16782959\), each of actual depth one. An exact
finite calculation in the *fixed field* \(\mathbf Q(\sqrt\beta)\)
shows that **none of the fifteen nonempty visible-only
orientation flips can come from a second primitive representation**.
This tests ordinary principality, giving a stronger rejection than
the earlier fixed-field genus condition alone. It uses no new
prime scan and does not expand any scalar coordinate.

The immediate consequence is conditional but exact: any new
positive primitive representation outside the original and
conjugate totally positive unit orbits genuinely splits the hidden
part \(H/V\). Indeed, if no hidden orientation changes, any nonempty
switch is one of the rejected fifteen. If all hidden orientations
change, complement the switch by conjugating the new representation;
one obtains only visible switches. The resulting conjugate element
has positive embeddings but possibly negative \(C'\); multiplication
by a sufficiently large positive integral Pell unit restores
\(C'>0\) without changing any orientation. Thus the two gcds from
a genuinely new orbit automatically give two nontrivial hidden
unitary factors. Existence of a new orbit is **not** proved.

## Why a switch would force a shared continued-fraction state

For a nonempty visible-only switch take \(d\mid V\) and the full
oriented ideal \(A_d\) of norm \(d\) in the maximal order of
\(\mathbf Q(\sqrt\beta)\). At each selected \(p\), its branch is
\(\sqrt\beta\equiv-1/c\bmod p\) since it divides the original
\(Z+C\sqrt\beta\). The mod-\(p^2\) orientation is the unique
Hensel lift of this root, **not** a claim that actual \(1/c\)
lifts as a root modulo \(p^2\) (indeed \(v_p(H)=1\)).
A hypothetical switch makes \(A_d^2\) principal, with totally
positive generator \(u\) and norm \(d^2\). As in the exact
[nominated-switch criterion](../rc-linked-scalar-H-oriented-switch-certificate-r1/ACTUAL-ORIENTED-FIXED-BETA-SWITCH-CERTIFICATE.md),
\(\beta\equiv1\bmod8\) and \(d\) odd force
\(u=x+y\sqrt\beta\) with \(x,y\in\mathbf Z\), by eliminating
the odd/odd half-integral coordinates. Keep the squared ideal
rather than \(A_d\) itself.

Take \(P\) modulo \(Q=d^2\) by CRT from the **negatives** of
the lifted roots. Then \(u\) belongs to the lattice
\(I=(Q,P+\sqrt\beta)\subset S=\mathbf Z[\sqrt\beta]\):
its root evaluation \(x-Py\bmod Q\) is zero because its
divisor is \(A_d^2\). The lattice \(I\) is an \(S\)-ideal
because \(P^2\equiv\beta\bmod Q\). Both \(uS\) and \(I\) have
index \(Q\) in \(S\), by the determinant of multiplication
by \(u\) and the displayed triangular basis respectively.
Thus \(uS=I\), with no suborder class-group comparison needed.
Comparing the two integral bases shows that
\((P+\sqrt\beta)/Q\) and \(\sqrt\beta\) differ by an integral
unimodular fractional-linear transformation.

Such equivalent irrational numbers have a common complete
quotient (the necessary direction of [Serret's theorem](https://arxiv.org/pdf/1706.00698)).
This direction also follows directly: integer translations and
positive reciprocation preserve continued-fraction tails. For
negation, with \(x=a+y,\ 0<y<1\), the next quotient of \(x\)
is \(t=1/y>1\), and that of \(-x\) is \(1/(1-y)=1+1/(t-1)\);
these have a common tail by the previous two operations.
Negative reciprocation inputs follow by conjugating with negation.
These transformations generate the full integral unimodular
action by the Euclidean algorithm on a matrix column.

## Exact exhaustive cycles, not a height bound

For a state \((P,Q)\) denoting \((P+\sqrt\beta)/Q\), the usual
continued-fraction step is
\[
 a=\left\lfloor(P+\sqrt\beta)/Q\right\rfloor,\quad
 P'=aQ-P,\qquad Q'=(\beta-P'^2)/Q .
\]
The denominator is nonzero and each division is checked exact.
With \(S_0=\lfloor\sqrt\beta\rfloor=452348193\), compute the
floor in integers as \((P+S_0+[Q<0])\mathbin{//}Q\), where
// is rounding down, not division toward zero. This holds
because \(0<\sqrt\beta-S_0<1\), including negative \(Q\).
Two states with the same complete quotient agree exactly by
irrationality of \(\sqrt\beta\). Once a state repeats, all
future states are already accounted for.

Take the actual \(W\) residues mod the four primes from the
source \((1,590,3027776569228\bmod2470991,
179011478283992\bmod16782959)\). Use literal
\(c=12W/(1+A)\). The source for \(W=1\bmod131\) is the
fixed formal-depth construction in ACTUAL-MATERIALIZED-SCALAR-SPECIALIZATION.md.
The other values come exactly from the independently checked
\(6551\) row and the exact two additional \(H\)-prime rows.
The checker uses these adjacent JSON files literally.
For initial \(P\) it computes \(t=1/c\bmod p\),
\(P_p=t+p((\beta-t^2)/p)(2t)^{-1}\bmod p^2\), with the correction
factor interpreted modulo \(p\), then CRT in the chosen subset.
It starts the principal normal form at \((0,1)\). That orbit
visits 265347 states, with first repetition at index 1
(a period of 265346). Each of the fifteen other starts reaches
a genuine repeated state, with roughly 264–266k visited states.
**None visits a state of the principal orbit.**
ACTUAL-VISIBLE-SWITCH-CYCLES.json contains all 15 starts and
their closure receipts. check_visible_switch_cycles.py
replays all exact states in seconds and checks every one against
the principal orbit; its safety stop is not used for rejection.

This proves that an independent new norm orbit cannot be
obtained by merely rearranging any nontrivial subset of the
known factors. It gives **no factorization or rank bound for
the hidden part**, and no rationality decision on the scalar
cover.
