# Independent review of the actual Kummer fibre's marked isogeny pairing

**Exact mathematical and byte replay PASS, 2026-11-21.**
The author's SHA256SUMS is
8d9c06e7ee4ee0a2f6a8c1935df3db20fa58ba1ff58f0875f60e7f3c36e41b52;
the paper is ffd713eea5c60e5932a0ec0d31ef89071bff94840ee561c9deff67e3a455fe78;
the archived replay is
072ced8cb3cac4a6e69d8487e692bfde86874edd4d9cc4487c7b0eec620beb69.

The literal substitution x=λt², y=λtV is the dual-isogeny covering
of E_d, so its torsor and pairing are on E′_d, not E_d. I checked
the orientation against [Fisher, §§2–3, §5 (8)–(9), f₂](https://arxiv.org/pdf/1509.03234).
At p≥5 dividing d the four rational 2-torsion classes give the
whole local E_d/2: an odd depth on every other-root difference
prevents a nontrivial rational half. When −3 is square, the
extra roots 2d(1±√−3) of E′ both have odd depth and give the
correct nontrivial second image; otherwise its image is trivial.
At 2 the 8-element E_d/2 gives the image sizes after the first
side's four unit classes; 105 is a square unit giving the 5
class on the second side. At 3 the distinct d and −3 classes
give the first side all four. No extra local equation on an
old basis column was omitted.

Thus the true signed kernel has only one row per split −3
prime of d. The actual old factors 5, 11, 17 remain inert and
give dim Sel(hatφ)≥5. The passage to Sel₂(E′_d) loses exactly
one dimension from the rational T₀ boundary; E′_d[2](Q) is
only the dual kernel. For rank one the rational image could
have dimension at most 3, so even that rank hypothesis would
leave dim Sha(E′_d)[hatφ]≥2, not identify the marked class.
The base shift X=x+1 gives Cremona 24a1 exactly; sign − of
the Ready twists is analytic parity, not rank. The fixed
binary form cannot use the stated [Wei–Zhai Theorem 1.1](https://arxiv.org/pdf/2607.18728):
its discriminant necessarily shares the prime 3 with the
reference conductor. Their comment about possible extensions
of the method is not the stated theorem and does not select
the original fixed c.

The conic through (β:1:0) leads to the stated f₂, whose
squareclass differs from t²−β only by a rational constant
with product of Hilbert symbols one. At odd λ depth the
actual branch t²=−3β gives a unit t²−β of class 3, producing
the stated (3/p) factor exactly when the partner has odd
valuation. At even λ depth away from old bad support, a zero
of one quadratic leaves the other unit, so the first
valuation is even (also at a t-pole). At the old sites
λ is square, and taking t near infinity kills the local
pairing. Thus an old-support partner contributes no sign,
even if its global admission is later established. The
separate norm test over Q(√−3) for those old-support partners
removes exactly the nonsplit places by local degree two.

The nonproduction D=1007 replay is genuinely negative:
e=803549 is admitted by the only split row at 409 and gives
(3/e)=−1. It excludes rationality on that fixed slope, not
on the whole Kummer surface, and it does not evaluate the
pairing on the original compact literal scalar. Vanishing
against every true partner would be a higher Selmer lift,
not a rational point. No Lean or remote write.

Reviewed by the independent proof/CI lane.
