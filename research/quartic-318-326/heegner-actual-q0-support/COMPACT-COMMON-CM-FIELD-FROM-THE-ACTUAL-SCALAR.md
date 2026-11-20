# One common compatible field from the exact scalar without expanding θ

Paper construction for the specific compact a=0 scalar at h=473592745039516333133760. This uses the actual rational circuit δ=1−b/17, not a surrogate W=1 (the latter is used only at explicitly verified local depths). It gives a same-field arithmetic candidate *before* choosing fresh I/q₀. It does not compute a Fourier coefficient, prove nonvanishing, or replace a prescribed h_* from the original analytic argument.

## Literal compact formula and every old split condition

Take t=21060 and set
```
M_CM = t²δ−1 > 0,
K = Q(sqrt(1−t²δ)) = Q(sqrt(−m)),
m = positive squarefree part of the rational M_CM.
```
In particular this field is specified by a short additional rational circuit in the very same δ, independently of its factorization or even of the expanded value of θ. The local statements are as follows.

- δ>8/9 and t≥2, so M_CM>0. At 2 and 3 the actual δ is a unit and t is divisible by 12, so M_CM≡−1 mod24. Dividing off rational squares preserves that residue (the square root factor is a unit at 2 and 3, with square 1 mod24), giving m≡23 mod24. Thus −m is a negative fundamental discriminant, with 2 and 3 split.
- At 53 the actual depth gives δ≡17, so M_CM≡41, a nonzero nonsquare: Euler’s criterion gives 41^26≡−1 mod53. Removing rational squares preserves this symbol. Since (−1/53)=+1, 53 is inert and prime to m.
- At each original β prime the actual c in b/17=βc² is integral and p|β, hence δ≡1. Therefore −M_CM≡1−t². In the original β-prime order the residues are (1,9,9,53,130,41,364,1087), all nonzero squares by the exact signed replay. In particular it is 1−t², not its negative, that is tested.
- For every actual prime p dividing θ, v_p(δ) is positive. Indeed p∤β and if v_p(c)<0 then v_p(δ)=2v_p(c) is negative even, impossible for a θ-prime; if v_p(c)≥0 then δ is integral. At such a p, −M_CM=1−t²δ≡1 independently of knowing the complete support. Thus p∤m and p splits. Equivalently, there is the actual norm identity
```
Nm_{K/Q}((1+sqrt(−M_CM))/t) = δ.
```
The direct local unit congruence additionally proves coprimality with each θ-prime.

This takes θ as the actual positive squarefree part of δ; none of the known primes or any possible additional ones is silently changed.

## Fresh prime choice and actual limitations

Given the genuine reduced c=C/Z, let H=Z²−βC² so δ=H/Z². The positive integer numerator A_CM=t²H−Z² represents the same field squareclass. At 2,3,53 and all β and θ primes, Z is a unit: at β this is c-integrality; at the other primes nonzero denominator valuation would give a negative even δ valuation inconsistent with its true positive or unit valuation. The proved local congruences therefore make A_CM coprime to all those primes, including 53. In a subsequent original selector one may require p≡1 mod A_CM and p>A_CM for each fresh p, which forces (−m/p)=(p/m)=+1 and does not conflict with the β-, θ-, 2/3-, 53- or previously chosen fresh prime moduli. This uses the ordinary reciprocity for odd fundamental −m just as in the earlier bounded field construction. The added 53 Legendre conditions can preserve the negative symbol of both d and dθ.

The benefit is an exact compact field from the scalar circuit, not an effective factorization of A_CM or of θ. Although the positive rational M_CM is less than t² in the real embedding, its squarefree part after clearing a square denominator can be enormous; no small bound on m is implied. This real local compatibility is not a nonzero coefficient for either sign and imposes no fixed old h_* choice. Actual completion requires the precise selector prime support and its trace/nonvanishing evidence.
