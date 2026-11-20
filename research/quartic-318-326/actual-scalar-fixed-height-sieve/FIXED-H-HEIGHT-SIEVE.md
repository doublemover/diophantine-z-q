# An exact auxiliary height bound for the fixed original scalar

Fix the actual materialized a=0 scalar at h=473592745039516333133760
and the same exact J/labels. No substitution W=1 is used except modulo
primes where that congruence was independently proved.

For any k=a/d with d≥1, the necessary discriminant equality becomes

    (d²H)² = β[9a⁴+(82D−18)a²d²+9δ²d⁴].

At any prime with integral D and δ, the right is integral. Accordingly
d²H must also be integral there, so the residue must be a square or zero.
This remains valid at primes dividing the denominator d; no inversion of
d occurs. It also holds regardless of whether a and d are coprime.

The adjacent exact script computes residues of the literal W and δ at
41 available finite primes 11≤p≤500. For each d mod p, a p-bit mask
lists all a mod p where the displayed form is a square or zero. The
mask is copied by multiplication by ∑ⱼ 2^(pj), then clipped to exactly
1≤a≤100000. Thus each bit exactly reflects the appropriate residue of
a, without a per-candidate arithmetic error or a heuristic rejection.
Intersect the masks for each 1≤d≤100000. Exactly 10^10 unsigned
nonzero pairs enter; no pairs survive the first 31 masks. The negative
numerators give the same result because the form is even in a.
The output lists the exact computed residues and shrinking cardinality
after every mask. Inaccessible local circuit poles are skipped, not
classified as failures. No candidate with k=0 was included; that case
requires H²=9βδ² and is impossible over Q for the actual nonsquare β.
The infinity branch does not contain a rational t.

So this **literal** scalar has no rational point of the auxiliary
β-class chart with k of rational height ≤100000; no global bound on
the height of k is known. Local solubility, survival of all finite
local tests by the projective torsor, and existence elsewhere on the
original two-parameter marked search are separate questions. The
computed lower bound does not imply the auxiliary curve has rank zero
or that the desired θ class lies in a nontrivial Tate–Shafarevich group.
