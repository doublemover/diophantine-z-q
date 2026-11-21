# A sparse exact barrier for the still-unknown denominator characters

Keep the original linked scalar's fixed \(h,J\), actual \(c=C/Z\)
and the alternate cover's local system. The earlier crossed-pole
lemma and CM count (84065756) imply that an odd extra prime of the
reduced denominator has a source \(h\)-pole in one of the split
completions of \(\mathbb Q(\sqrt2)\), an \(i\)-pole in the other,
and splits \(2,-1,7,-R\). This note searches the exact sparse
Gaussian locus, not all primes below a huge bound.

Let \(q\) be such an exceptional prime. Source reduction is a
quadratic twist of \(y^2=x^3-x\) with \(q\equiv1\bmod4\).
The original quartic-character Jacobi sum count gives
\(\#E_-(\mathbb F_q)=q+1-2a=|(a+b\mathrm i)-1|^2\) for
some \(q=a^2+b^2\), choosing the sign of \(a\) to match the
actual completion with its \(i\)-pole. The real coordinate \(a\)
is odd: the source has full rational 2-torsion, and otherwise
\(q+1-2a\) would be 2 mod 4. The CM order proof already shows
\(2^{47}\mid\#E_-(\mathbb F_q)\). Therefore \(\pi-1\) is
divisible by \((1+\mathrm i)^{47}\) for \(\pi=a+b\mathrm i\).
No choice of abstract Frobenius basis or exact sign oracle is
needed here; the count suffices.

Set \(S=2^{23}\). There exist integers \(u,v\), with \(u\equiv
v\bmod2\) and \(v>0\) after conjugating if needed, such that
\[
       q=(1+Su)^2+(Sv)^2 .
\]
Indeed \((1+\mathrm i)^{47}\) is a unit times
\(S(1+\mathrm i)\). A Gaussian integer is a multiple of
\(1+\mathrm i\) exactly when its coordinates have the same
parity. One cannot have \(b=0\) for this prime \(q\).
The formula also gives \(q\equiv1\bmod2^{24}\) exactly.

The adjacent pure Python program enumerates **all** such
pairs with \(u^2+v^2\le65536\) (including signed \(u\)).
It discards only witnessed composites, proven by a small
factor or a strong compositeness witness; it does not infer
primality from passing these tests. It then requires the two
remaining necessary signatures \((7/q)=(-R/q)=1\).
At every surviving possible prime, the program checks
\(\sqrt2\) exactly and computes both \([h]R_0\) by literal
finite chord-and-tangent operations, with \(h\) itself (no
unverified scalar reduction). The proposed translated index
annihilator would be verified before any use, but in this
run it is never needed: the remaining 783 candidate prime
rows all have no \(h\)-pole in either source completion.
There are no unresolved computations.

For a pair outside this disk,
\[
 q\ \ge\ \bigl(S\sqrt{65537}-1\bigr)^2
\]
by the reverse triangle inequality in the Gaussian plane.
Taking the integer ceiling yields the exact new support bound
\[
 q\ \ge\ 4611756382876565506.
\]
This concerns only additional odd denominator factors:
the four known fixed normalizer factors are unchanged,
and a source pole of even depth gives no contribution to
the denominator squareclass. The result still does not prove
that the exceptional part of \(Z\) is trivial or give any of
its Legendre signs. In particular it does not choose an
actual \(\tau\), decide the alternate curve's rational
solubility, or find a new \(C/L'\) prime.

The repeatable arithmetic is:

    sha256sum -c SHA256SUMS
    PYTHONDONTWRITEBYTECODE=1 python3 check_exact_denominator_grid.py | cmp - EXACT-DENOMINATOR-GRID.json

The script reads only the exact \(h,J\) from the already
published scalar JSON in the named adjacent directory.
