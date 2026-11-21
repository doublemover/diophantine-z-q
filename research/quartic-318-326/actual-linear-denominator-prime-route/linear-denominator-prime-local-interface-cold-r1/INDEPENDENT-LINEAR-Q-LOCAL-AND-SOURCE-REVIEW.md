# Independent local and original-source audit of the linear denominator prime

**Pass in the stated local/source scope.** This review binds
the exact paper LINEAR-GAUSSIAN-PRIMES-TO-ORIGINAL-READY-POLES.md,
SHA-256 29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0.
It does not independently certify the affine-linear Artin prime mass
or the ambient four-variable upper sieve; those are separate checks.

## The order-only prime

The source definitions in SelectedFormalEntry318 refer to the
same original half-point \(R\) on the short model, not its double.
On the extra \(q\), exact per-arm order divides the appropriate
quarter count by SelectedQuarterOrder318.actual_order_dvd_quarter,
given the actual Gaussian ray's local roots and signed count.
The per-prime counting statement is CanonicalSelectedCounts318.actual_count;
it is not intrinsically tied to a square-key row. The canonical CM
count and correct sign choice on both orientations remain the same
original mathematical inputs, not consequences of an arbitrary
annihilator.

Including \(q\) in both quarter LCMs suffices for
\(M_-\mid h\) and \(M_+\mid(h-1)\) on its respective arms.
SelectedFormalEntry318.near and ValuativeOrbitMultiples318.near_int
then give literal formal depth at least one at the base and each
integer label multiple. No \(q\mid\Pi\) or \(q^3\mid h\) enters
this step; do not call the old selected wrapper that requires \(p\mid\Pi\).

The mod-16 ray gives \(v_2N(\pi-1)=6,v_2N(\pi+1)=2\);
after division by four it contributes exactly a factor 16 on
the minus side and an odd plus side, even at \(q\). Odd wheel
avoidance on all positions gives \(\gcd(M_-,L)=16\) and
\(\gcd(M_+,L)=1\); cross gcd four gives
\(\gcd(M_-,M_+)=1\).
Only the contact primes occur in \(\Pi\). A contact prime cannot
divide its own even plus norm, which is positive and less than
twice it. For distinct contacts the common band also puts the
shift norm below twice the candidate divisor, and separation
excludes equality. The plus norm at \(q\) is smaller than the
least contact prime. There is correctly no test of \(q\)
dividing a selected plus modulus across positions other than
the ordinary cross-neighbor gcd: \(\Pi^3\) omits \(q\).

## Genuine Padé arms, fold and pole

On the primary formal arm apply ActualPrimaryLogPrecision318.original_ratio
at \(R=1\), with the primary identity of ActualSourceRatioParameters318.
Its bound is at least four for the difference from the integer label,
so the exact ratio is integral. On the opposite formal arm use
ActualAlternateRatioPrecision318.alternate_precision directly,
which assumes Near at depth one; its first linear branch and the
three full Padé branches all have integral ratios. These statements
refer to the same two stored ratio families of ActualPadeRatios318.

For the other half of each family the points reduce to the literal
fixed \(R,n_jR\) or \(-R,-n_jR\), since the relevant \(h\) or \(h-1\)
multiple reduces to the origin. The rational charts \(U,V\)
are regular there after a fixed finite exclusion. Original \(U(R)\),
\(V(R)\), every needed \(V(n_jR)\), and \(Q_J(V(\pm n_jR)-1)\)
are nonzero by the chart-domain source; the labels are fixed and
nonzero. The exact nonformal alternate common denominator is the
fixed quotient at \(\pm R\)
\[
 (-U/V)\,P_G(DU^4)/Q_G(DU^4).
\]
At index \(h=2\) the source actual_commonLog_ne and common_parameter
give this nonzero expression; negating \(R\) changes only the
sign of \(U\), leaving the other factors determining nonvanishing
unchanged. Deleting the finitely many rational norm
numerator/denominator primes for these fixed quantities is adequate.
There is no exclusion depending on the newly selected \(h\).

Checking ActualDetectorFold318.leaves against DetectorGateWitness318
and PadeRatioWitness318: the first coefficient is the square of
the actual \(w_{37}=N(U_h)\), the second is from the actual \(f_V\),
and the remainder use the eight chart slots and original ratios,
with a fixed finite set of rational coefficient denominators.
Both embeddings are integral after the exclusions. At the split
odd \(q\), extracting the rational and imaginary components
uses the units 2 and \(\sqrt2\). Thus all sixteen literal
unweighted leaves are integral.

In ScaledContactWeights318, write \(s=c_j^2t\),
\(\Delta=s-1\), and \(g=c_j^{10}\Delta^2/F(s)\).
The three fold weights are exactly \(g,g^7\Delta^{18},g^{25}\Delta^{72}\).
Here \(c_j\) is a \(q\)-unit,
\(v_q(s)=v_q(\Delta)=-1\), \(v_q(F(s))=-5\), so
the respective weights all have depth 3. Starting at 1, each
of the sixteen actual square-plus-leaf steps is therefore
1 modulo \(q\) in both embeddings. Hence the original trace
quotient \((X^2-2Y^2)/(2X)\) is a unit. The literal pole is
\(\tau^2F(s)/(c_j^{10}\Delta^6)\) and has valuation \(+1\),
not a negative odd denominator. At a genuine contact all
the old strong primary/opposite hypotheses apply with the
same leaf depths by \(v(F)=1\) and unit \(c_j,\Delta\);
these local formulas do not require a global square denominator for \(t\).
Away from the genuine selected primes the factorization alone gives
even \(v_p(F)\), since \(c_j^{10}/(D Q)^{10}\) is a square
and the extra \(q\) is a unit. It is the product of the integer
prime factors that is automatically a unit there; \(F\) may include
a nonunit fixed scale. The pole's remaining factor is a square,
so only negative odd depths could obstruct denominator parity.

## Literal 2/3/17 preparation and final consumer

At \(2,3,17\), the same \(q\equiv1\bmod408\) is a square unit.
Use \(d_p=DQ\sqrt q\) and a sequence \(d_n=DQ z_n\) of
integer approximants with \(z_n\to\sqrt q\).
They are finite-place units in the multiplier \(z_n\).
The actual normalizations in DetectorPrimeProduct318.linear are
\[
 u-\theta_i d_n^2/c_j^2=u+k_{ji}Q^2z_n^2.
\]
All are integers, and are nonzero square units at that \(p\)
because \(u\equiv1\bmod408\) and \(Q\) is fixed sufficiently
deep. The depth condition on \(d_n\), same \(h\) progression,
and converted casts are exactly SourceLocalProgression318.Prepared.
It applies to the approximants, not to a fictitious global square
root of \(q\). The rational pole at the target has genuine nonzero
denominators: \(\Delta,F\) and the real chain from the exact
real domain, and the prior chart divisions depend on \(h\), not \(t\).
An algebraically nonzero rational denominator remains nonzero in
the local field, so continuity works even if it is not a local unit.
The subset of squares (including zero) of depth at least the
required threshold is closed in \(\mathbb Q_p\). The target
pole is nonzero by its real range, so preserving that threshold
and squareclass by passage to the limit gives the original
nonzero conditions at 2,3,17.

ThreeDetectorCRTWitness318.prepared_family takes arbitrary
sufficiently large rational \(t\) and the five CRT conditions.
The exact Ready predicate in OriginalJoinedPrimeSource318
is a predicate of the stored \(b\), containing its real range,
square denominator and the three local square/depth rows,
but no square-hypothesis on \(t\) and no PointPair.
PreparedIntegerSource318.complete_at_index also quantifies
over arbitrary rational \(t\), and consumes original h, guards,
rows, four actual PointPairs and the original scalar anchor.
This paper supplies the same Ready data (with the original
retained scalar preparation) at that original interface.
It intentionally does **not** inhabit OriginalJoinedPrimeSource318.Pattern,
or supply the four PointPairs, the row-287 anchor, or square-key
native wrappers. No Lean build was run.

The paper's printed source prefixes checked match the exact
sources for the local audit, including ActualAlternateRatioPrecision318
48606002, ActualSourceRatioParameters318 d670034b,
ActualPrimaryLogPrecision318 d2c6bc48, ActualDetectorFold318
1bb3b85f, ThreeDetectorCRTWitness318 837caa15,
PreparedIntegerSource318 e3ecec83, SourceLocalProgression318
cd5f09f0, ThreeDetectorArithmetic318 6afbbd9c, and
GaussianQuarterModuli318 f2c36cd8, SelectedQuarterOrder318
de0a4151, CanonicalSelectedCounts318 0fdaf3f9.
Additional typed-source checks: SelectedFormalEntry318 c0d4d58b,
CompressedChartDomains318 c093c081, ScaledDetectorChain318
94984f53, ScaledContactWeights318 13431f1c,
DetectorGateWitness318 5c6c6153, DetectorPrimeProduct318
1b887cab, and OriginalJoinedPrimeSource318 a0adb7ca.

Signed: independent local/source reviewer, 2026-11-21 UTC.
