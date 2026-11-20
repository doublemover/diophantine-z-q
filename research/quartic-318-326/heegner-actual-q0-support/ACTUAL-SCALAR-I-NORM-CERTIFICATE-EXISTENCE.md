# A factor-list-free existence and certificate for the true I incidences

This is an exact paper option for the seven I slots of the original scalar selector. It does not produce numeric primes, complete the unproved q₀ row in general, or assert any coefficient is nonzero. Keep the actual positive rational δ=1−b/17 at the fixed h,J, its actual squareclass θ, the eight fixed β primes, and the compact common field K=Q(sqrt(1−21060²δ)) of 2794fcc1….

## I from a principal norm, without listing θ primes

Let F=Q(sqrt δ)=Q(sqrt θ), and H⁺ its narrow Hilbert class field (ray class field for the product of the real places). This is defined without expanding θ. By class field theory (e.g. [Milne, Class Field Theory, Ch. V, Example 1.7(b) and the ray class reciprocity theorem](https://www.math.ucsd.edu/~csorense/teaching/math204B_W19/Milne_CFT.pdf)), H⁺/F is unramified at all finite primes and its trivial Artin class is a totally-positive principal ideal. H⁺/Q is Galois: the nontrivial automorphism of F preserves the class-field modulus and its narrow ideal group, hence preserves the associated field. Its finite ramification is supported only on θ, the positive odd fundamental discriminant of F.

At a given I stage collect all **other** fixed conditions, namely:
- p≡1 mod24;
- the exact prescribed β column e_i+e_8;
- mutual symbol + with each previously chosen I, for example p≡1 mod each prior prime;
- p≡1 mod53;
- p≡1 mod the compact K-defining positive integer numerator A_CM of 2794fcc1, which makes p split in K.

The transitive reciprocity signs in these conditions agree with the original I incidence: p≡1 mod4 so the indicated local signs transpose without change. All these congruences give a unit ray a mod M by CRT. Lower bounds on p ensure distinctness and allow the previous I primes to be coprime to A_CM. The whole integer M is prime to θ. Therefore H⁺∩Q(ζ_M)=Q: any intersection is unramified at every finite rational prime (the ramification sets are disjoint), impossible for a nontrivial number field by Minkowski's discriminant bound. In the actual compositum, Chebotarev gives infinitely many primes in the ray a mod M with Frobenius identity on H⁺. Neither proof contains the full θ factor list as input.

For such a prime p, a prime ℘ of F over p has degree one and is totally-positive principal ℘=(α). Thus its integral generator has positive norm p. Write α=x+y sqrt δ, x,y∈Q, y≠0 since a rational square cannot be p. Then the following single literal rational certificate verifies the entire otherwise unknown I row:
```
δ=(x/y)²−p(1/y)².
```
Indeed at any q|θ we have q≠p, q odd, and v_q(δ) is odd. If q were inert in Q(sqrt p), every local norm would have even valuation in this unramified quadratic extension, contradiction. Thus (p/q)=+1 for **every** actual θ prime. This is not merely aggregate quadratic reciprocity. It imposes full I support even though theta's primes need not be listed to specify the selection proof. The selected primes still need to be obtained as numbers with the norm certificates if used for an effective witness.

## Optional independent common Frobenius on the actual residual 13 packet

If desired, the same search can impose any specified conjugacy class in GL₂(F₁₃) on the actual residual g representation. It has field L₁₃=Q(E₋₁[13]), group GL₂(F₁₃) (proved in 6003a528…), is unramified outside 2,3,13, and its maximal abelian subfield is Q(ζ₁₃) by the determinant/commutator calculation. In this construction M is prime to 13: the old β and every prior fresh I avoid 13, and the compact numerator A_CM is a unit at 13 since 21060 is a multiple of 13 and the actual δ is a unit. Hence Q(ζ_M) and L₁₃ meet trivially. Their compositum is still unramified at every θ-prime, since θ avoids 2,3,13. It therefore also meets H⁺ trivially by the same discriminant argument. Now prescribe all three components simultaneously by Chebotarev, e.g. residual trace zero and determinant 3 as in the nonexceptional coefficient arguments. This does not mean a Hecke operator at p changes the squarefree twist index, or that the actual prime-shape coefficient is a unit.

## Conditional q₀ variant and exact remaining source

The original q₀ is not a principal norm from F in general, since it may need nontrivial (q₀/q) signs at θ primes. A useful sharply scoped variant: **if** exactly one additional θ prime remains beyond the four actual known ones, the checked determinant computation f1916bfd… fixes its q₀ bit to 0 and the first four bits are already (0,1,0,0). Then use the narrow Hilbert class field of the residual positive class F_rest=Q(sqrt(δ/(131·6551·2470991·16782959))). Select q₀ split there while the CRT ray enforces its exact original β/I/type/53/compact-K conditions and the first four θ symbols. The ramification supports are again disjoint and the one unknown bit is certified by a norm. The hypothesis of exactly one additional θ prime is not proved. Similarly, any separately proved valid completion with all unseen bits zero can use this same residual-field selection. The general differentiated remaining q₀-row is not chosen here.

Even when every prime slot can be chosen arithmetically, the exact missing modular assertion is still a unit coefficient at the resulting product n=β∏I q₀; for the genuinely paired same-field detector the four reads at n,nθ,mn,mnθ have to concern the same primes and m. The present argument produces neither one of those reads nor eventual insertion of one of the existing arbitrary-support nonzero coefficients into this prescribed pattern. It improves the arithmetic support selection and a verifiable norm certificate only.
