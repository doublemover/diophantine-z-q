# A materialized actual a=0 scalar index with compact labels

Exact arithmetic/paper contract, no build or complete detector tuple.
All definitions refer to the current original workflow (baseline
558a130e12a461d9b380b44510d457f0d3d8a29d).

    a=0; A_label=B_label=0; N=65536; M=d=1.
    R_input=4376874610839020; A_scalar=114444 R_input.
    h=473592745039516333133760.
    J=15007791093853300881634594756184038091213022964893463173481091096131436857094464566857888173451545095125082924125704203009720761127663357842915750000000.
    s=1+6^15*3^65536*J, k=2(s−2).
    labels=(3723,s,U_{k+1}(s),U_k(s)/(s−2)).

Here U_0=0, U_1=1, U_{i+2}=sU_{i+1}−U_i. These are the
explicit positive odd Lucas witnesses of
`LucasSequence318.positive_odd_witness_at_index` and
`source_positive_odd_witness`; not an assertion they are
definitionally the opaque Classical.choice. They satisfy the
same relations, and `PreparedIntegerSource318`'s actual
`scalar_domain` and `complete_at_index` accept these labels.
The scalar value depends on the labels only through s, by
`ScalarActualInputs318.detector33/37`,
`ScalarForwardWitness318.N,Q,W` and the input identity.

## Finite local certificates and choice of least numbers in this design

In the literal model y²=x³−E x, E=(3−√2)², the generator
R=(1+√2,2√2) doubles to the original P. The stored orders
refer to R at every local residue field of
S={2,3,5,11,17,163,661,733,1489,1861,13,37,53,131}
except the ramified prime 2. They are not the orders of P.
At each odd p in S this model has good reduction because
the discriminant is 64 E³, whose only prime divisors lie
over 2 and 7. The script obtains a multiple of the order
inside the Hasse interval by baby/giant matching; the order
certificate itself just requires [m]R=O and
[m/q]R≠O for each prime q|m. Factorization of the finite
m is by trial division. The two distinct residues at split
p are checked separately; nonsplit p uses F_{p²}.

Take the least positive h divisible by these orders, 64, and
131 (whose local order 44 is coprime to 131). For odd p in
S every [h]R lies in the formal group. At infinity its usual
parameter z=−x/y satisfies u=2y/(x²+E)=−2z+O(z²),
hence v_p(u)=v_p(z). At all chosen odd p the fields are
unramified. The formal logarithm on their maximal ideal
preserves valuation, so v_σ(u([b]T))=v_σ(u(T))+v_p(b)
for integer b≠0 and formal T; this applies to both split
embeddings and the single inert embedding (norm doubles
valuation in the latter). At 131 the extra factor of 131
gives v_σ(u)≥2. At 2, instead use
`ActualOrbitBranchDepth318.two_u_place` and
`ActualOrbitCoefficientDepth318.two_chart`:
v₂Norm(U(4m))=7+2v₂(m), both coefficients have
valuation ≥1+v₂(m). These formulas give the same norm
valuation change 2v₂(b) under integer multiplication on
this progression, with all nonzero-index conventions.

Put I=Norm(U(s−1)), using literal
`ScalarTranslatedIndex318.scalar_inverse_norm`;
H=Norm(U(h)), f=Re(U(h)²). Choose the least positive
J for the following sufficient simultaneous condition:
`h * ∏_{p∈S} p^{ceil((15 v_p R_input + 1)/2)} ∣ s−1`.
The exact formula is the required modulus divided by its gcd
with 6^15 * 3^65536. This is not an exhaustive global
minimality certificate among *every* locally admissible h or
J. It is exact minimality for the displayed formal-depth
construction (label chosen after h).

For each odd p, integrality of both local coefficients
follows either from both split valuations (division by
2√2 is by a unit), or from the inert integer basis. They
both have depth ≥1, ≥2 at 131; at 2 use the stronger
2-adic bound above. Since all odd support primes have
v_p(R_input)≤1, and v₂(R_input)=2, this implies

    v_p(H)>v_p(R_input), v_p(2f)>v_p(R_input),
    v_p(I)−v_p(H) = 2 v_p((s−1)/h) ≥15 v_p(R_input)+1.
    
Thus Q=I/(H R_input^15) lies in pZ_p; N_pack=1+
(H/R_input)²+2f/R_input≡1 mod p. At 131 N_pack≡1 mod
131² by the stronger depth. The literal W=N_pack²+
R_input Q² is 1 mod p for the full support and extra
primes, and 1 mod131². `prepared_of_units` yields the
actual scalar square denominator, 2/3/17 valuations and
local square assertions. If a progression is wanted,
h'=h(1+t∏S) leaves *each* of the norm-valuation formulas
unchanged, and the same fixed s works at every such
positive h'. No choice of new labels after selecting h'.

## Actual guards and real margin

Use the reduction at p=5, where R has order 5 and [h]R=O.
Since 5|s−1, the Lucas recurrence modulo 5 at s=1 has
period 6, k=2(s−2)≡4 mod6, and (t_L,z_L)≡(−1,1) mod5.
Here k≡4 mod6 follows independently from s≡1 mod3 and s
odd; dividing U_k by s−2 modulo 5 is valid since s−2≡−1.
At the four labels, the first reciprocal abscissas
reduce to 0 because [label·h]P reduces to O, where 1/x
is regular and zero. The second reciprocal is that of
[−label]P=[−2label]R. The script certifies these avoid
x=0 in F25, so all reductions are legitimate. Their
coefficients re are (4,1,1,1), nonzero. These certify
the literal `RealGuardTrace318.guardValue` nonvanishing
without any giant real label evaluation; no sign requirement
is used, consistent with `complete_at_index`.

To test the only strict required real threshold, compute
U(h) in the two real embeddings using binary signed secant
and tangent, with rational dyadic directed outward rounding.
The script encloses √2 using integer isqrt, and checks that
all denominators are separated from zero before dividing.
It certifies Norm U(h) > 1/100 (approximately +0.13677).
The first index h of the constructed local progression already
passes, so is its least admissible positive member. The proof
uses exact interval endpoint integers, not rounded display.
`PreparedIntegerSource318.scalar_domain` now proves positivity
and the upper endpoint (and its packed estimate gives b<1e−4).

## What is materialized and what is still infeasible

The single index, scalar label s and both Lucas *recipes*
are exact, with a compact integer circuit for this actual b:

    b=A_scalar [W/(1+A_scalar)]²,
    W from H,f,I above,
    δ=1−b/17, θ=sf(δ).

No W=1 substitution is made. The previous finite-ray
certificates apply to this exact b, and (131\mid θ).
Full θ requires evaluating/factoring the reduced numerator of
this literal δ, not factoring the surrogate value at W=1.
Before expanding that numerator one can test local δ values
by field or finite-depth p-adic arithmetic, without knowing θ.

Sizes: h has 79 bits, s has 104414 bits, and k=2(s−2)
has 104415 bits. The Lucas values as integers are not short:
for m≥1, `(s−1)^(m−1) ≤ U_m(s) ≤ s^(m−1)`,
by induction on successive positive ratios; thus the
expanded U_{k+1} alone needs at least k(104412)+1 bits,
already over 2^104430. For conversion using expanded
elliptic coordinates, x([i]R) has logarithmic projective
height 2 i² ĥ(R)+O(1) over K, by the bounded
Weil/canonical-height difference and nontorsion R. This
gives quadratic expanded height in i at both required
indices h and s−1, about 2^208826 to 2^208828 times a fixed
coefficient at the large index. This is the bit barrier
of explicit group-coordinate expansion, not a claimed
information-theoretic lower bound for the reduced final
rational b (where cancellation would need a separate proof).
A modular reduction of the compact circuit instead needs
only O(log(s−1)+log h) group additions at most and modest
prime-power precision; at ordinary good primes one first
reduces by the true finite orders. No global rational
θ-class point or rationality obstruction follows from
these certified local or size data.
