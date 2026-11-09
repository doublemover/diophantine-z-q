# Exact coherent root signs before prime choice

Author: /root/advance_integer_witnesses. Frozen four-module packet. Fresh strict serial replay and a recursive private-inclusive audit of34 declarations passed. Distinct source review and admission remain pending.

## Exact result

For every four integer labels n_j, every common integer index h, and every slot j with n_j!=0, the literal source root computed from the coherent charts equals exactly

    -1/u([n_j]R),

whenever its literal rational real-part denominator guard is nonzero. The right-hand side is the earlier fixedRoot(n_j), independent of h, and the sign is the historical negative sign. This closes the sign ambiguity recorded in the preceding coherent-chart packet. It does not assume that the emitted root equals a prechosen root, and it does not choose a sign after selecting h or primes.

The charts are exactly those of CoherentMultipleCharts318: u(T)=2y/(x²+D), v(T)=(x⁴-6Dx²+D²)/(x²+D)², extended at O by(0,1). The two half-points for a slot are [n_j h]R and [n_j(h-1)]R. The actual underlying source points are [n_j h]P and [n_j(h-1)]P, with P=2R.

## Proof and domains

1. CoherentSecantPolynomial318 proves a universal cleared polynomial identity for two points y²=x³-Dx and b²=a³-Da. Put d=a-x, L=-b-y, X=L²-(x+a)d², Y=L(xd²-X)-yd³, q=x²+D and r=a²+D. With vnum(x)=x⁴-6Dx²+D², the identity is

    2Yd(q²r²+16Dy²b²)
      =(2y vnum(a) q-2b vnum(x) r)(X²+Dd⁴).

A small included SymPy generator computes two polynomial coefficients whose combination with the two curve equations gives this identity with remainder zero. The emitted Lean linear_combination proof checks those coefficients through ring proofs in the kernel. SymPy is not a proof oracle; it only writes the explicit certificate. The universal polynomial lemma needs only a field, and all its coefficients and factors remain present.

2. CoherentSecant318 applies the polynomial to the actual Mathlib subtraction of finite half-points with distinct abscissae. The actual slope is(-b-y)/(a-x), and the actual difference coordinates are X/d² and Y/d³. It proves every division condition: d!=0 from the supplied distinctness, q and r nonzero by the actual positive real D, and X²+Dd⁴ nonzero because it equals((X/d²)²+D)d⁴. Clearing denominators, including the common factor2 in the rational identity, yields the oriented relation

    u(Q-S)(1+D u(Q)²u(S)²)=u(Q)v(S)-u(S)v(Q).

This is an equality of u-coordinates, not merely of their squares or underlying doubled points.

3. CoherentOrbit318 constructs all needed secant hypotheses on the actual integer orbit. A vanishing nR would imply nP=0, contradicting the previously proved actual nontorsion theorem for n!=0. Thus n↦nR is injective. The adjacent half-points [nh]R and[n(h-1)]R cannot be equal because n!=0. They cannot be negatives because that would give n(2h-1)=0, impossible for integer h and nonzero n. The actual Point.eq_or_eq_neg_of_xRep_eq_xRep theorem then rules out equal abscissae. There is no unproved genericity assumption or omitted tangent case.

4. CoherentRootSign318 extends the u-subtraction identity through either identity input directly, using u(O)=0,v(O)=1 and u(-Q)=-u(Q). The finite/finite branch uses the proved secant identity. The difference [nh]R-[n(h-1)]R=[n]R is checked in the actual group, so the formula holds for every integer h, including0 and1, and either sign of n.

5. For U=u([nh]R),V=v([nh]R),A=u([n(h-1)]R),B=v([n(h-1)]R),C=u([n]R), the two quartic curve equations give

    (UB+AV)(UB-AV)=(U²-A²)(1+DU²A²).

The coherent subtraction formula identifies UB-AV=C(1+DU²A²). The latter denominator is nonzero by positivity under the actual real embedding. Cancellation gives(UB+AV)C=U²-A². The literal guard makes A²-U² nonzero in K, and C!=0 follows from n!=0. Dividing gives the actual source quotient(UB+AV)/(A²-U²)=-1/C, with the exact required sign and no lost scalar.

6. emitted_root_fixed consumes the original RealGuardWitness318.root and denominator and the actual CoherentMultiplePrefix318 Fin8 chart arrays. Fin.append_left/right checks the exact source slot mapping. The input guard is the literal rational real-coefficient guard; the proved denominator_ne supplies its K nonvanishing. The source/global D equality is explicit. The result is the same fixedRoot used in the preceding packet, not a new normalization.

## Historical comparison and boundaries

The original connecting argument was read in progress/receipts/completeness-work/COMPLETENESS-ASSEMBLY.md, Section3. It fixes the coherent rational charts, shows the emitted root is one rational-function square root throughout its domain, and evaluates its sign at O. Historical disposition: prior justification found. This packet formalizes an alternative exact secant/polynomial route to the same all-index signed identity, rather than claiming a new historical gap or relying on an unformalized function-field argument.

The preceding coherent packet is unchanged: its sign ambiguity was the explicit boundary at that earlier frozen stage. The present theorem closes that boundary for every guarded actual integer chart. It allows the four signed roots and any expressions in them to be defined independently of h before prime choice. It does not yet assemble all literal product/scale storage rows, prove all scale inequalities/local values, choose primes or h, or produce a complete source witness.

Actual real orbit topology and identity-component cover, analytic guard pullbacks and scalar-region nonemptiness, arithmetic prime/CRT/local preparation, the remaining237 rows and the full integer-to-source/final quartic theorem remain open.

## Verification

All four final sources received fresh serial strict Lean4.35.0 checks with -j1 -M6144 -Ddebug.skipKernelTC=false and explicit packet root. The recursive audit enumerates all34 private/generated declarations in those four modules and allows only propext, Classical.choice and Quot.sound. Frozen dependencies are the two coherent-chart sources and the two real-guard sources, plus114 exact baseline source pins. The included generator is also bound. No shared source or main manifest is changed and no clean upstream rebuild is claimed.
