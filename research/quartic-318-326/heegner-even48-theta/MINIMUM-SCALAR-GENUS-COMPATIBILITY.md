# Bounded genus-field compatibility at the actual minimum scalar support

**Scope.** This is arithmetic preflight for the literal original
scalar input \(a=0\) or \(a=-1\), not a completed linked pole,
not a new all-place selector theorem, and not a computed
nonzero analytic companion for that input. Here \(h\) always
means the original shared point-imposed chart index; \(h_*=-m\)
is the separately chosen analytic CM discriminant. They are
not interchangeable.

## Exact support and smallest fields tested

The actual scalar coefficient has the form
\(b=A(W/(1+A))^2\), where \(A=114444R(a)\). At \(a=0,-1\),
\(R=4376874610839020\), and
\[
 A=500907037962860804880,\quad
 \beta=204618888056724185=5\cdot11\cdot17\cdot163\cdot661\cdot733
    \cdot1489\cdot1861 .
\]
Thus \(\beta\) is fixed independently of the tiny real value
of b and independently of any proposed chart \(h\). All eight
primes in \(\beta\) must split in the analytic CM field.
\(m=455\) fails even before adding auxiliary primes
(5 is ramified, 11 and 733 inert).

A deterministic bounded scan finds the least positive squarefree
\(m\equiv23\bmod24\) splitting those eight primes and inert at
53 is the prime \(m=14159\), with class number 173. The next
choices begin 14231, 24719, 48839, 59399, 63839. Source
checked_minimum_scalar_f53_candidates.py SHA ecf1c456… and exact
output MINIMUM-SCALAR-SUPPORT-ADMISSIBILITY.json SHA 80c3f4c2….
\(n\) for the **core-only bounded example** has 68 decimal digits,
with the seven I-primes
173617, 228841, 784081, 1774609, 2405209, 7638601, 16357489
and distinguished prime 25918747. All primalities and selected
incidence signs pass; all new primes exceed the displayed
test threshold 76176. No threshold is claimed for an unknown
future ambient source. This is not the original selected tuple
on completed scalar \(\theta\); it numerically checks the
additional constraints can coexist with the unchanged core incidence.

If an actual \(131\mid\theta\) is forced, \(m=14159\) fails:
\((-14159/131)=-1\). The first compatible fixed-prime precheck
switches to \(m=14231=7\cdot19\cdot107\), with class number
164, and still does not check any remaining \(\theta\) primes.
There are exact optional core examples with that split test,
old I-to-131 symbol +1, and both requested q0-at-131 signs;
see minimum_scalar_131_compatibility.py SHA 9abe6aed… and
MINIMUM-SCALAR-131-COMPATIBILITY.json SHA 44e8fe7e….
No selector uses \(\theta=131\) (indeed a stand-alone 131 is
not the required \(\theta\bmod24=1\)). Actual q0-to-J signs
belong to the enlarged incidence determinant.

## The full \(\theta\) test and a genuine baseline obstruction

Write the literal \(W=w/e\) in reduced rational terms. Since
\(A/17\) is integral at this input, put
\[
 H=(1+A)^2e^2-(A/17)w^2,\quad
 r_\theta=V/B^2=1-b/17=H/((1+A)^2e^2),\quad\theta=\operatorname{sf}(H).
\]
Here \(H>0\) by the actual scalar domain. This identity ties
\(\theta\) to the *same* prepared \(W\); replacing \(W=1\)
globally is not allowed. If \(W\equiv1\) at an extra prime \(q\)
with unit denominator, then \(H\equiv e^2 F\) there for
\[
 F=(1+A)^2-A/17=250907860680726875559825159650206985141521 .
\]
At 53, \(F\equiv25\) and \(1+A\equiv25\); the resulting
\(r_\theta\equiv17\) is a nonzero square. Thus the compatible
local \(W\equiv1\bmod53\) guard (handled separately in the
genuine chart) preserves \(\theta\) as a local square and
makes \(H\) itself prime-to-53. Since the selected \(\theta\)
is odd and \(\theta\equiv1\bmod24\), the same chosen n of
type \(11\bmod24\) can then be used for both p53 detector
types, provided n has \(\chi_{-n}(53)=-1\).

For any squarefree \(m\equiv23\bmod24\) with \((m,\theta)=1\),
quadratic reciprocity gives
\[
  \left(\frac{\theta}{m}\right)
  =\prod_{q\mid\theta}\left(\frac{-m}{q}\right).
\]
Full splitting forces +1, not merely unit status at \(m\).
If one *also imposes* the baseline \(W\equiv1\) at all of
7,19,107, then \(F\) and \(1+A\) are units there and the
three signs of \(F\) are (+1,−1,+1). This excludes complete
\(\theta\)-splitting for \(m=14231\) in that stronger baseline,
despite 131 itself splitting. It does not exclude a different
actual \(W\) satisfying only the earlier 53 control.

The first bounded candidate passing the eight \(\beta\) primes,
131, inert p53, and the additional *baseline* Jacobi test is
\(m=59399\) (prime, class number 269), followed by 63839.
For 59399, \(F\equiv30930=20586^2\) and \(1+A\equiv23913\).
This is a necessary/product check even when its actual local
square condition is imposed: two unknown inert primes would
pass it. In particular, 13356527 is inert in the 59399 field;
one cannot also force that divisor into \(\theta\) for this
choice. Scripts checked_scalar_baseline_genus_options.py SHA
b6b43c0e… and SCALAR-W1-GENUS-OPTIONS.json SHA a1a8ec8d…
record these signs and actual bounded core I/q0 arithmetic
for both possible 131-symbols. The displayed examples do
not substitute a single subfactor for the complete \(\theta\).

## Exact preserving conditions when the full input becomes available

Given the original actual support, keep every prescribed old
symbol. If fresh I/q0 are still being selected, adding separate
congruences \(I_i\equiv1\bmod24\), \(q_0\equiv19\bmod24\),
split signs at \(m\), and p53 signs with total −1 is compatible
with the existing Dirichlet construction **when their moduli
are disjoint from the fixed support**. For example impose
\(q_{\mathrm{new}}\equiv1\bmod m\) for the split condition;
the original mod-12 classes and all selected incidence signs
remain unchanged. We read these as optional refinements at
that existing quantified selection, not as permission to
rechoose a tuple that was already fixed.

There is also an exact existence argument that needs no
factorization of \(H\) just to *find an admissible field*.
If \(Hn\) is prime to 53, take a prime \(m\) in the CRT
class
\[
  m\equiv-1\pmod{\operatorname{lcm}(24,H,n)},\qquad
  (m/53)=-1 .
\]
The class is invertible, so Dirichlet applies. It splits every
actual odd prime of \(n\theta\), because \(-m\equiv1\) at
every prime of \(Hn\), and gives the required types at 2,3,53.
The exact \(h,W,\theta,n\) and already-selected tuple are
unchanged. This choice may make \(m\) impractically large;
it is not an assertion that the previously found small
fields pass the full support. It is legitimate only while
the analytic partner is not itself prescribed already.
As an alternative sufficient check for a small fixed m,
an actual \(r_\theta=x^2+m y^2\) together with \((\theta,m)=1\)
forces even valuations at every inert prime. This is a true
norm condition, not a consequence of \(W\equiv1\bmod m\).

The varying-m CST ratio to the nonzero 323 reference merely
replaces \(d/d_0\) by \(\sqrt m\,d/(\sqrt{455}\cdot323)\);
the two fixed local type ternary factors cancel it as before.
Thus the same fixed source theorem can handle such a partner
with full support, but its second norm grows as \(md\).
No nonzero mod-13 coefficient has been computed for any
of these large admissible examples. If a proof branch needs a
nonzero analytic companion in advance, a positive further
quadratic twist preserving all displayed local classes may
be selected by [Waldspurger local nonvanishing, ST Theorem 6.9](https://arxiv.org/html/2107.04483#S6),
starting with the sign-+ compatible companion. That assertion
changes the field and is for one fixed elliptic form at a
time; it does not make the original selected m any smaller,
nor give simultaneous nonvanishing for two different forms.

If the actual finite detector is eventually nonzero, its
nontorsion check cannot use q5 here, since \(5\mid\beta\).
For m14159, q19 is inert and therefore good for any compatible
d, with counts 16 or 24 over F19 and 384 over F19², prime
to 13. At m14231, q7 is ramified; at m59399 q7 is inert.
Their compatible d are good at 7 and have counts 8 and 64.
More generally one may pick a good prime outside all current
supports with the same mod-13 Frobenius conjugacy as 7 on
\(E_{-1}[13]\), which has neither eigenvalue +1 nor −1.
Then twisting preserves absence of both, and reduction over
a degree-at-most-two residue field excludes 13-torsion. This
conditional argument keeps the actual fixed detector and
does not fill any missing analytic, rank, or native proof.
