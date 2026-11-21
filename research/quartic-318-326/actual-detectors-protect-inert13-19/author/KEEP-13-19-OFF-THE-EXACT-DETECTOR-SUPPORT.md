# Protect 13 and 19 before the original linear-q detector selection

This is a refinement of the exact original same-index preparation,
not a new source model and not an assertion that every already fixed
\(\theta\) avoids these primes. It makes the independent inert 13 and
19 reductions permissible on the corresponding selected twists.
It does not make either trace nonzero.

## 1. Literal bounded coefficient balls before choosing any prime

Start with the published linear-\(q\) branch: fixed input and fixed
nonzero labels, fixed detector scales \(c_j\ne0\), clearing \(D\),
and initial scalar-ready \(h_0\bmod L\) with \(64\mid h_0,L\).
Choose an integer \(h_*>1\) on this initial progression and in the
original real guard region. This exists by the same
\(\mathsf{CompactDetectorRegion318.mixedCRT\_access}\) used to
read the original prefix, with \(\Pi=M_+=1,\ M_-=16\).
The choice does not depend on the later contact or denominator
primes. Its purpose is local regularity, not selecting the final
source index.

For each \(\ell\in\{13,19\}\) work simultaneously in both embeddings
or the single quadratic completion of the source field
\(\mathbf Q(\sqrt2)\), as appropriate. The unweighted literal leaf
coefficients are rational functions of the finite chart tuple
on the integer orbit at \(h_*\), independent of the free \(t\).
In particular the original \(\mathsf{ActualPadeRatios318}\)
gives the nonzero field denominators of all the actual Padé
expressions when the index is neither zero nor one. The earlier
coherent charts have the same source-domain hypotheses. Thus
these functions are continuous at the chosen rational orbit
point in every completion, even if some values are not integral
there. Pick a neighborhood on which all finitely many coefficient
valuations are bounded below. This uses no uniform bound over
unconstrained choices of \(h\).

The local elliptic groups are compact. In any sufficiently
small open subgroup, the source point has a finite return time:
its class in the finite quotient has finite order. By taking
these return periods for all places above both primes, refine
\(L\) to a multiple \(L'\) and require \(h\equiv h_*\bmod L'\).
The chart inputs formed by addition of fixed points and
multiplication by the fixed labels are continuous, so this
ensures the same coefficient bounds for **every** later legal
\(h\) in that congruence. The argument uses local point
periodicity to preserve a neighborhood, not identity of all
\(h\)'s exact rational chart values. Scalar-readiness and
\(64\)-divisibility are retained.

## 2. Deep \(t\) makes all three literal \(\delta_j\) square units

Place 13,19 and all new divisors of \(L'\) in the fixed base
wheel, before choosing any genuine prime form. The existing
Gaussian base recipe chooses \((0,1)\) at ordinary odd base
primes (and keeps the prescribed residues at 2 and 7).
The norm and both translated norms there are 1 and 2.
Thus the expanded wheel has the same required nonempty
base ray, odd quarter-order avoidance, and original contact
coprimalities. The later cutoff makes every genuine prime
\(u,q,p_k\) distinct from 13 and 19. Including these fixed
primes only changes a fixed modulus in the original argument.

Increase the exact powers of 13 and 19 in \(Q\) in
\(t=u/(D^2Q^2q)\), before the genuine prime selection.
For \(T=c_j^2t\) choose \(v_\ell(T)<0\) and less than the
valuations of all nonzero roots of the monic original quintic
\(F(T)=T(T+1/2)(T+1)(T-1/2399)(T+32/407)\).
Then \(v_\ell(F(T))=5v_\ell(T)\) and
\(v_\ell(\Delta)=v_\ell(T)\) for \(\Delta=T-1\).
The three exact folded weights are \(k,k^7\Delta^{18},
k^{25}\Delta^{72}\), with \(k=c_j^{10}\Delta^2/F(T)\).
Their valuations are respectively
\[
10v_\ell(c_j)-3v_\ell(T),\quad
70v_\ell(c_j)-3v_\ell(T),\quad
250v_\ell(c_j)-3v_\ell(T).
\]
Hence these increase without bound even when a fixed scale
is nonunit. Make them strictly positive after addition of
every bounded unweighted coefficient valuation. At each
completion the literal fold now starts at 1 and stays
congruent to 1. Equivalently its real component is 1 and
imaginary component 0 modulo \(\ell\). Here both \(\ell\)
are unramified in \(\mathbf Q(\sqrt2)\) and integral
coordinate extraction in \(1,\sqrt2\) preserves this
congruence in the split and inert cases. Consequently the
literal trace quotient \((R^2-2I^2)/(2R)\) is a unit.

The actual pole is the square of that unit times
\(F(T)/(c_j^{10}\Delta^6)\). Its valuation is therefore
\[
          -v_\ell(t)-12v_\ell(c_j)>0
\]
after the chosen depth increase. This is also even because
\(u,q\) are units and \(t\) has denominator \(D^2Q^2\) there.
Since \(\ell\ne17\), the literal \(1-b_j/17\) is a square
unit at both tested primes for each of the **same three**
detector poles. The prime-form selection follows the original
argument, with the real rectangle chosen after \(Q\); final
mixed CRT access then produces one \(h\) with the old real
guards and this new local modulus. No independent h is used
for different poles.

## 3. What this buys

The exact \(\theta_j=[1-b_j/17]\) avoids 13 and 19 and the
same holds for the exact \(\beta_j\) by its protected-prime
profile. Choose any new helper and repair primes outside
13 and 19. The old selected pair can then impose on its one
shared \(q_0\) two independent quadratic residue choices
at 13 and 19 as in the two static receivers. There is no
obstruction from the other arm's \(\theta\) support, since
neither prime appears in the full support. This provides
admissible genuinely small odd-order target receivers
for the exact selected original curves. It still supplies
neither normalized CM coefficient nor a rational point.
The fourth scalar-pole and anchor problem is unchanged.

## Exact inputs

- Published linear-\(q\) paper SHA-256
  29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0.
- ActualPadeRatios318.lean:
  536503bb576c233ab948145db9d323ea5f28b5c96bacb6b1953fced45ea74244.
- CompactDetectorRegion318.lean:
  1c10c2100f36502e87a4c5b24eb5a733ce39b3458ad5abfc310d032c1cbf6cd7.
- ThreeDetectorCRTWitness318.lean:
  837caa15e52f368f9a2e98443e4b410bd64884fbf7b456dd9053eab9fd6812d0.
- ScaledDetectorChain318.lean:
  6b40c47012f0ded449545deed449ebb4659b0268f4edad9e079e556626cd436d.
- ActualDetectorFold318.lean:
  1bb3b85f8bc3ca7bd58c252ebda8b416b7011905a212a6aae7ec9c1ee5513cf5.
