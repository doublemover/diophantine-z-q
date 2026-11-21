# Independent review: positive-root quotient and an actual local-global counterfamily

**Verdict: exact paper proof and arithmetic controls pass.** Binds
author note SHA-256 dc8a9e1591d9d0a798f8cd9fd332af6c8d5e7aa0a40e2b02f36bd3c67318bd02,
manifest adb654f1eba0027340561dd11d907645584b412f8d1f93683af286c7a32b63cc.
All author files hash and the literal finite checker output is
byte-identical to e0b76917013e4eaaa67279b6690609a31ea1cca645776e2d86daf6f5f907e2aa.

I checked the five actual quotient maps: the four independent radical
characters over the squared line give exactly the four cubic products
and one quartic product of genus one. The reciprocal map on the
quartic product uses \(K=-abc\,stu\) and multiplies the ordinate by
\(K/z^2\), which produces the stated monic cubic and all three signed
root squareclasses. These checks identify the literal positive-root
pair and its marked [2]-cover, not just an elliptic curve with a
related invariant. The enumerated dimensions \(3,3,2,3,2\) refer only
to the coefficient-supported subspaces, not their full Selmer groups.

For the actual \(E_{bc}\), the raw classes (bc,c,b) and (1,bc,bc)
are independent modulo rational torsion. The zero-root torsion row
has negative second coordinate since t,u,b,c are positive; either other
torsion row has first class \(bc\cdot2399\), unlike any combination
of the two marked supported rows. Removing the unique valuation
row at \(q_c\) gives exactly \(A^*=(u,b\Delta,bu\Delta)\) and
\(F^*=(1,-2399,-2399)\). Both become locally trivial at the
variable prime. Weil evaluation of \(F^*\) is along the root-zero
torsion line and pairs with the first coordinate of \(A^*\),
giving the oriented cup \(\chi_{2399}(g)\chi_{-2399}(h)\).

Independently, if \(\psi=a+2A\) records the fourth-root action and
\(\varepsilon\) the action on i, the twisted addition of two exponents
mod 4 has carry \(b(a+\varepsilon)\), where \(b\) is the second
low bit. Thus \(d\Gamma(g,h)=\chi_{-2399}(g)\chi_{2399}(h)\).
The coboundary of the pointwise product of the two quadratic
characters is their sum in both orders, correcting the orientation.
At the variable primes both quadratic bits and the i-character
vanish; the restriction is exactly the quartic sign of 2399.
The fixed local ratios of the twists are squares throughout the
bad set of the base \(E_{b p_c}\), and the primitive is unramified
outside 2 and 2399. Thus the proof of [Smith's Theorem 3.2,
eq. (3.3)](https://arxiv.org/pdf/1607.07860) applies to the two
ordinary normalized classes; no other local correction is used.

I independently checked the two residue classes at the inert
2399-place of \(\mathbf Q(i)\). The unit \(g=(5+i)/(5-i)\) has exact
norm one; the two constrained residues have equal norm 1489
but opposite tame quartic signs. Unit ambiguity of a Gaussian
generator is harmless: \(2399^2-1\) is divisible by 16, so any
fourth root of unity has trivial fourth-power residue character
in \(\mathbf F_{2399^2}\). The two unit norms are not 1, so neither
residue is ±1. The earlier fixed index and both old point-order
caps are prime to 2399 by the literal count residues. The old finite
order/torsion layers are therefore unramified there and independent of
the isolated ray contribution by the trivial unramified intersection
over the Gaussian field. The quartic extension is cyclic and tame
of degree four locally by Eisenstein; only its factor at 2399
changes (keep the same dyadic pilot phase, at enough conductor).
This preserves the *full rational norm congruence* at the fixed
modulus, the other retained phases, the exact point-order cap,
the tail argument and the local pointed 4-cover on \(E_{ab}\).
The source checks show existence of a clone in each sign branch,
not a conjectural independent unrestricted Artin choice.

The two branches have opposite actual ordinary Cassels–Tate
signs against the checked supported row. In the nonzero branch,
a rational point on the genus-five curve would induce a rational
point on the literal two-positive-factor degree-four [2]-cover,
so its marked class would be rational Kummer and pair trivially.
This is a global torsor argument, also applying to an exceptional
fiber, and the genus-17 pullback maps to the same genus-five curve.
Thus one branch is a genuine local-global counterfamily while
retaining the exact named squared cells and the selected \(E_{ab}\)
4-cover. The zero branch only passes this one test: no rational
point, absolute branch identity, numeric clone primes, simultaneous
all-quotient orthogonality, or Lean result is asserted.

Signed: independent reviewer /root/high_review_ci.
