# An actual new Gaussian ray phase independent of the original index anchor

Fix the exact XVI detector (`EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json`) and
its even index congruence h* mod L. Write the literal scale quotient
η=c₁/c₂=m/n in lowest terms, n>0, and P=407m²+32·2399n². Its discriminant
difference has rational class δ=[2399·407·P]; the individual root classes
are s=[−814] and t=[2399]. Here and below δ means t−s when a value
rather than a squareclass is needed.

The checked reciprocity identity (4731ab04…) gives (2399/P)=−1:
P≡7 mod8, (P/2399)=(407/2399)=+, and P is odd and coprime 2399.
At every p|P outside the exceptional set {2,7,11,37,2399},
(−814/p)=(2399/p); this follows directly from
407(m/n)²=−32·2399 mod p and p∤mn. The exceptional primes do
not divide P by the previously checked unit rows (in particular the
correct p7 row is P/n²≡3 mod7). Hence some actual prime ℓ|P has odd
depth and both symbols negative.

**This prime can be required to be outside L.** The full L has 78
distinct prime factors; the checker verifies each by trial division,
divides out its exact exponent and ends at 1. Exactly 28 of these
are eligible for both signs to be negative. At each of them the checker
verifies all the true Ū factors are defined at the corresponding reduced
four original labeled points, and finds integral η with
407η²+32·2399≠0 in the residue field. This is independent of depth and
says none of these 28 primes divides P. For each arm only an actual
annihilator is needed (verified by direct finite-field scalar
multiplication), not a CM trace formula or an exact order. The labels
are computed by the doubled Lucas recurrence, stripping the full part
of s₀−2 supported at primes dividing the annihilator before division,
where s₀=1+6¹⁵·3⁶⁵⁵³⁶ J. At the origin the chart is regular with
value zero; at every affine point the actual denominator is a unit.
Over split primes both residues are evaluated, and over inert primes
the first coefficient of the quadratic product is half the trace.
Thus the noncollision check is on the same rational η, not a
chart-selecting value. No prime outside L is enumerated.

It follows unconditionally that there is an odd ℓ∤L with
vℓ(P) odd and (2399/ℓ)=(−814/ℓ)=−1. In particular ℓ∤2·7·814·2399,
ℓ is outside the sixteen contacts, and ℓ divides the saturation
support B because it divides the squareclass of the actual root
difference. At this ℓ, δ has odd valuation and s,t are units. The
literal order torsion and division fibers of the original selection
are unramified above ℓ (their prime levels divide L and the
actual curves have good reduction off 2 and 7). The Gaussian ray of
ℓ-power modulus is therefore independent of the order field **after
its own ℓ-ray component is separated**. This gives a prime at which
a norm residue can toggle the δ-character of a future prime
q≡1 mod8, without toggling the s- or t-character. It is not yet a
computed ℓ, a new actual Q-point or a Selmer-four result.

Replay with Python standard library:
```sh
python3 -B check_anchor_collision_phases.py /path/to/EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json | cmp - EXACT-ANCHOR-COLLISION-PHASES.json
sha256sum -c SHA256SUMS
```
