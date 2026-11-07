# Physical-anchor completeness, with all local places and the affine domain

## Exact statement

Let A,S be rational numbers, S≠0, and suppose r=A/S is integral at 2 and 3. Then there exist rational u,v,w such that

`u²+6v²−2w²−3A²+2S²=0`.

This is the exact unsheared physical-anchor equation used by the 318 source. No positivity, archimedean size bound, or denominator-square condition on A is required.

Put `c=3r²−2` and `q(x,y,z)=x²+6y²−2z²`. We prove q represents c over Q.

## 1. The place 3

Because r∈Z₃, c≡1 mod3. Thus c is a nonzero square in Q₃ by the ordinary odd-prime square/Hensel criterion. Take `(x,y,z)=(sqrt(c),0,0)`.

In particular c is nonzero as a rational number. This guarantees that the four-variable form used below is nondegenerate.

## 2. The place 2

There are three exhaustive cases, including r=0 in the third:

1. If r is a 2-adic unit, then r²≡1 mod8, so c≡1 mod8. Take `(sqrt(c),0,0)`.
2. If v₂(r)=1, write r=2k with k a 2-adic unit. The number `3k²−2` is 1 mod8. Choose s with `s²=3k²−2` and take `(x,y,z)=(2s,1,0)`. Then
   `x²+6y²−2z² = 4(3k²−2)+6 = 12k²−2 = c`.
3. If r∈4Z₂, write r=4k. The number `1+8k²` is 1 mod8. Choose s with `s²=1+8k²` and take `(x,y,z)=(0,s,2)`. Then
   `x²+6y²−2z² = 6(1+8k²)−8 = 48k²−2 = c`.

Each invoked root exists by the 2-adic unit-square criterion. These formulas are valid for rational r with the stated local integrality; r need not be an ordinary integer.

## 3. Every prime p≥5

Over F_p, the sets of squares and `2−6·(squares)` each have cardinality `(p+1)/2`, hence intersect. Consequently there are residues x,y satisfying `x²+6y²=2`. This gives a nonzero isotropic vector `(x,y,1)` for q modulo p.

Its z derivative is −4, a unit modulo p. Hensel's lemma lifts it to a nonzero vector e in Q_p³ with q(e)=0.

Let B be the symmetric bilinear form associated to q. It is nondegenerate at p≥5, so choose f with B(e,f)≠0. For any desired c,

`q(f+t e)=q(f)+2t B(e,f)`.

Choosing `t=(c−q(f))/(2B(e,f))` represents c. This argument works even at primes dividing the rational numerator or denominator of c. There is no omitted finite exceptional set beyond 2 and 3.

## 4. The real place

Choose z large enough that c+2z²>0, set y=0 and x=sqrt(c+2z²). Thus q represents every real c.

## 5. Global existence and the affine denominator

Consider the nondegenerate rational form

`Q(X,Y,Z,T)=X²+6Y²−2Z²−cT²`.

The preceding constructions give a nonzero zero with T=1 over every completion of Q. Hasse–Minkowski gives a nonzero rational zero `(X,Y,Z,T)`.

It remains essential to prove T≠0. The ternary form q is anisotropic over Q₃. To see this, scale any hypothetical nonzero Q₃ zero until X,Y,Z∈Z₃ and at least one is a unit. Reduction modulo 3 gives X²+Z²=0, which forces both X and Z divisible by 3. The original equation then forces 6Y² divisible by 9, hence Y divisible by 3, a contradiction. Therefore q has no nonzero rational zero either.

If T were zero, the first three coordinates of the global zero would give such a nonzero ternary zero. Hence T≠0, and dividing by T yields rational x,y,z with q(x,y,z)=c. Finally take `(u,v,w)=S(x,y,z)` to obtain the exact physical anchor.

The use of Hasse–Minkowski is standard local-global quadratic-form theory; the nonzero-zero formulation was checked against [Conrad, Theorem 3.3(2)](https://kconrad.math.uconn.edu/blurbs/gradnumthy/localglobal.pdf). It is an explicit input here, not a new unproved Artin or elliptic-converse assertion. The local constructions and the nonzero-affine-denominator argument above establish all its hypotheses.

## 6. Verification for the current 318 witness choices

The construction in `COMPLETENESS-ASSEMBLY.md` uses

`S=3^65536`, `A=Nu_R+4096 S n_C`.

The scalar point and four fixed odd roots give

- `v₂(Nu_R)≥0` and `v₂(n_C)=−12`;
- `v₃(Nu_R)≥65536` and `v₃(n_C)=0`.

Therefore

`A/S=Nu_R/S+4096 n_C`

is integral at 2 and 3: the factor 4096=2¹² exactly cancels the possible 2-adic denominator of n_C, and the chosen scalar depth at 3 clears the S denominator. These are the current source's exponent and shear, not the older anchor constants.

After choosing u,v,w as above, the source's fixed invertible rational shear supplies its stored raw anchor witnesses. No change to X, to the selected elliptic points, or to any already fixed root sign is needed.

## Verification scope

`AnchorLocalCharts.lean` kernel checks the explicit algebraic charts, their residue checks modulo 8 and 3, the homogeneous-to-affine step under an explicit anisotropy premise, and scaling back to the physical equation. The proof of the p-adic square criteria, Hensel's lemma, and Hasse–Minkowski is not formalized in that file. This distinction is separate from the source-specific mathematical proof above.

The independent helper has additionally proved rational anisotropy by integer descent in `../prime-witness-bridge/AnchorAnisotropy.lean`. Its `homogeneous_denominator_nonzero`, `rational_representation_of_homogeneous`, and `physical_anchor_of_homogeneous` require no anisotropy premise. The only global producer still needed for that final bridge is the rational homogeneous zero supplied by Hasse–Minkowski. The independent local-soundness reviewer checked the mathematical local cases and affine-domain argument and found no mismatch.
