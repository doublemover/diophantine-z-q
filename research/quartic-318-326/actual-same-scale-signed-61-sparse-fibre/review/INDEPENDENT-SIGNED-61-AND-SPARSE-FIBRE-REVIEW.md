# Independent cold review: signed mod-61 statistic and sparse fibre

Signed: independent mathematical reviewer, 2026-11-21. PASS on
both exact source-only notes on the already reviewed lower semistable
curve. I verified every author manifest entry and replayed both Python
outputs byte-for-byte. The signed-statistic r2 is the clean display-only
successor of the independently reviewed r1; its Python and JSON are
unchanged. No actual selected twist, nonzero genus trace, modular map
or Lean compilation was computed.

## Exact signed statistic

Author `joined-semistsable-61-signed-statistic-r2` manifest
7876a82f7fee56636f24659f3c0d9e7664f141f44bf971536ad284e5e49a5225,
paper 8e75136ec97c9f10a41f9128630714b7aac073991ea3b986141b83fd36730b75,
checker 57ad7da520a6c39bc6a9e34f6bdfcc3a2713fc640bcf809b08f1bbfdf8e78a4c,
result 7388dc3791bbe155406c223123991b18d3af5dafab2cfb7f1883a90e6df41373.

The prime-square residue count 3808=224*17 and the actual generator
g=[4](1,23) guarantee that [224] on the term values lands in the same
rational order-17 line and differs from [4] on the full trace by a
unit. The marked terms obey v_(ha)=psi(h)v_a, not ordinary equality:
the genuine ramified Atkin–Lehner signs match the genus character,
and rational cusp constants vanish in this order-17 projection.
The unique full relation among ramified ideal classes shows H is
free of order eight and C/H has at least sixteen labels. The
geometric freeness is separate: a fixed W_m label would give
u^2=±[m] by its two marks at m; + forces a scalar of impossible
square degree, and all seven minus candidates contradict a
preserved residual line. Actual Frobenius has reflection
a -> nu*a^(-1)H with psi(nu)=-, and its sign on v is also minus,
so the SIGNED class values are constant on this involution.
The exact unaveraged statistic has the factor 8 and weights one or two
according to orbit size, not a division.
An unsigned histogram cannot force nonzero even with these
equivariances, as two same-sized sign orbits give distinct outputs
with the same histogram. This gives no counterexample realized
by geometric CM values.

The five supersingular geometric j labels at 61, scalar square
Frobenius on each prime-to-61 torsion line, and the primewise
level marking product give 3,151,872,000 ambient labels,
393,984,000 exact H orbits and at least 12,312,000 full
Atkin–Lehner/Frobenius label orbits. These are label cardinalities,
not runtime bounds. The D=1 class canary is unselected: 49,176
reduced forms, 6,147 H orbits, with exact signed balances and
no recorded modular-map values.

## One exact zero; conditional sparse fibre

Author `joined-semistsable-61-sparse-fibre-r1` manifest
a0183731a218fbfbee92091b7d014cb8c2ce6acba274a715b0924d3be96fa7ce,
paper 1052bcdb1a4f08dbdc3dcf054fb1c7306d941028f93909bbe97e43ad4474c715,
checker ff0104b18863e8087608f615d3cb801f6fb88c09c36d3082b9af1b01e9f4abcf,
result b0e5efcbe56af873804a11e032f1e13e96ed972b535948a46da55e4ab5eda0de.

I checked the exact normalized 2-isogeny by substitution and
differential, the self-isogeny differential trace 1, and
the degree <=8 argument forcing its Frobenius conjugate to
equal 1-gamma. The anticommuting I,F,IF yield the literal
endomorphism of square [-251895]. The chosen seven cyclic
lines are actual kernels or eigenlines, so the geometric
marked label is W_m-fixed and has precisely zero order-17
coordinate. This is not a statement that its original image
point is zero, nor a selected genus-trace calculation.
The characteristic-zero discriminant -251895 zero control is separate.

The true nonrational 17-line has k-Frobenius 15; the dual
cyclic isogeny kernel is constant. A supplied actual fibre
would read the Frobenius translation exactly, and the index-17
image of the isogeny contains the whole prime-to-17 rational
subgroup. No pullback fibre equation is supplied. At primitive
17 normalization, connected optimality plus the degree-prime-to-17
isogeny makes elliptic Picard pullback injective even in the
good special fibre. The actual character line's nontrivial
Frobenius eigenvalue excludes Kummer equations of modular units:
every geometric cuspidal divisor is fixed already, regardless
of the constant extension. The separate noncongruence proof
lifts the geometric prime-to-61 Picard line into characteristic
zero, not its arithmetic Frobenius to a complex loop.
Local congruence images at the seven level primes have no
17 quotient, and all other full local SL2 groups have no
abelian quotient by elementary commutators. This excludes a
congruence cyclic model, not any noncuspidal or direct
arithmetic fibre model. The exact same-map nonzero detector
remains uncomputed.
