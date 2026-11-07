# Coherent +1 branch: explicit residue-field certificate

The current 318 construction uses the normalized curve

`E: y² = x³ − (3−r)²x`, `r²=2`,

and `R₀=(1+r,2r)`, with `P=2R₀`. At the opposite selected place, the common index is chosen so that the doubling-image order divides h−1. To infer that the *specific coherent* chart has v=+1, rather than merely that its square is 1, one needs R₀ itself in the doubling image. This is stronger than knowing that P is a double.

## 1. The ray implies 2 is a fourth power using only quadratic reciprocity

Let `p=a²+b²` be a selected prime with `a≡9 (mod 16)` and `b≡0 (mod 16)`. Then `p≡1 (mod 16)`, gcd(a,b)=1, and neither a nor b vanishes modulo p. Also a+b is nonzero as an integer and modulo p. The inequalities `|a+b|≤sqrt(2p)<p` hold because p>2.

Write Jacobi symbols with positive odd denominators. Signs in the numerators are harmless because p≡1 mod 4.

First, quadratic reciprocity gives

`(a/p) = (p/|a|) = (b²/|a|) = 1`.

The formula includes |a|=1 with the usual Jacobi convention. The gcd condition justifies the last equality.

Second, put `q=|a+b|`. Since a+b≡1 mod 8, q≡±1 mod 8, so `(2/q)=1`. The identity

`2p = (a+b)² + (a−b)²`

and gcd(a−b,q)=1 give `(2p/q)=1`, hence `(p/q)=1`. Quadratic reciprocity therefore gives `(a+b/p)=1`.

In F_p let `i=b/a`. Then `i²=−1`, `ab=a²i`, and `(a+b)²=2ab`. Raising the last identity to `(p−1)/4` yields

`1 = (a+b)^((p−1)/2) = 2^((p−1)/4) a^((p−1)/2) i^((p−1)/4)`.

The a factor is 1 by the first Legendre-symbol calculation. The i factor is 1 because 4 divides `(p−1)/4`. Thus `2^((p−1)/4)=1`. The cyclicity of F_p^× implies that 2 is a fourth power.

This proves exactly the needed special case of the usual Gaussian quartic supplement, without assuming the full quartic reciprocity law. It works for either sign of a and b. The ray condition modulo 7 is not used in this step.

## 2. Root-of-unity algebra

Because 16 divides p−1, choose a primitive sixteenth root z in F_p. Then z⁸=−1. Choose t with t⁴=2 by §1. Either root r of 2 is a square: r=±t², and −1=(z⁴)².

Put `i=z⁴` and `q=z²+z⁻²`. The identity z⁸=−1 gives `q²=2`, so q=±r. Also

- `(z+z⁻¹)² = 2+q`;
- `[i(z−z⁻¹)]² = 2−q`.

Thus 2+r is a square for either r. Dividing its square root by a square root of r gives a square root a₀ of 1+r, because `(2+r)/r=1+r`.

This entire algebraic step, including both choices of r, is kernel checked in `BranchHalving.epsilon_square_from_roots`. Its premises are exactly r²=2, z⁸=−1, t⁴=2, and characteristic different from 2. The existence of z and t is supplied by cyclicity and the preceding elementary number theory, not silently embedded in the Lean theorem.

## 3. An explicit half of R₀

Given `a₀²=1+r`, define

`u=a₀+r/a₀`,

`x_Q=1+2r−2u`,

`y_Q=−2+10r−(r+4)u`,

`m=2−u`.

Here a₀ is nonzero, and `u²=5r−1`. Direct polynomial identities give

- `y_Q²=x_Q³−(3−r)²x_Q`;
- `2y_Qm=3x_Q²−(3−r)²`;
- `m²−2x_Q=1+r`;
- `m(x_Q−(1+r))−y_Q=2r`.

The last three identities are the tangent and duplication formulas. The denominator y_Q is nonzero in characteristics other than 2 and 7. Indeed if y_Q=0, the curve and tangent equations force x_Q=0 and then `(3−r)²=0`; together with r²=2 this would force 7=0.

Therefore Q is a well-defined affine point and 2Q=R₀. `BranchHalving.explicit_half_from_roots` kernel checks the whole combined algebraic certificate over arbitrary fields. It does not assume characteristic zero, so it applies to the selected residue fields.

## 4. From the doubling image to the literal branch

The selected finite curve has full rational two-torsion and characteristic other than 2. Therefore the doubling map has kernel size four, and the doubling image has order d₊/4. By §3, R₀ lies in that image; hence `(d₊/4)R₀=O`.

The source CRT makes h−1 a multiple of every opposite d₊/4. For each fixed integer nᵢ, the point `[(h−1)nᵢ]R₀` therefore reduces to O at the opposite place. Its globally fixed duplication-chart values are

`u(T)=2y/(x²+D)`, `v(T)=(x⁴−6Dx²+D²)/(x²+D)²`,

extended regularly at O as u(O)=0, v(O)=1. Thus the coherent values satisfy u≡0 and v≡+1. There is no post-selection sign choice, and no additional p-power divisibility of h−1 is needed for this branch claim.

The kernel-checked file certifies §§2–3. The elementary reciprocity argument in §1 and the finite-group/formal-chart interpretation in §4 are mathematical proofs recorded here, not claimed as additional Lean results. None of these statements proves simultaneous existence of the prime patterns or the restricted pole converse.

Independent review: the local-soundness worker checked §1 separately, including both absolute-value denominators, the gcd(a−b,a+b) step, and the p≡1 mod16 exponent. No sign or Jacobi-symbol issue was found.
