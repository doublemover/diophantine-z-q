# Faithful transfer to the reduction of the one original point

The two source-only owners here are independent of the final ZMod
generic producer and independent of the local norm adapter. The
supplied generic identity is exactly its mathematical output: the
literal Gaussian scalar at the chosen root on E's ZMod p generic
point equals coordinateHom of stock Frobenius on that same point.

## The actual comparison step

Let K be the residue field of the original prime w, let P be the
given original primitive point, and set Q=red_w(P). Infinity is
fixed by additivity. Otherwise write the exact Q=(x,y). Over the
formal field K((t)), choose the genuine nonzero origin arc T from
PowerSeriesArc.formal_origin_arc, and lift Q by the *constant*
coordinate embedding. Compare the same generic identity twice:

1. At T: its abscissa is outside the valuation ring, because
   specialize(T)=O. Strict ValuedPolynomialPole supplies faithful
   polynomial evaluation at this actual abscissa.
2. At T+constant(Q): strict stock mixed addition computes actual
   integral coordinates X,Y. Stock reduction is additive and says
   their residues are those of the constants x,y. If X were its
   own residue lifted as a constant, X=C(x). The literal cubic
   forces Y²=C(y)² and Y=±C(y). In the minus case equal residue
   forces y=−y; the two constants then coincide. In every case
   both coordinates would be the actual constants, contradicting
   T+constant(Q)=constant(Q) since T≠O. Thus X is nonconstant.
   Strict ArcFunctionEmbedding.eval_integral_arc_injective yields
   faithful polynomial evaluation on the exact X. There is no
   y≠0 assumption, and this also works at residue 2-torsion.

In both evaluations restrict the exact embedding to the same
ZMod p coefficients: polynomial map is injective under the chosen
coefficient map, and eval₂_map gives the actual composition.
Strict ArcFunctionEmbedding.arcEmbedding extends these injections
to the actual generic chart field, reads both actual arc coordinates
and sends constGeneric(s) to the same embedded s. The actual stock
Gaussian endomorphism is compatible by coordinate_gaussian.
The actual power Frobenius is compatible by the coefficient map
power law f(x^p)=(f(x))^p (and y likewise), not the false assertion
that every constant in K or K((t)) is fixed by Frobenius.

Since both stock point maps are additive, the two equalities at T
and T+constant(Q) cancel to equality on constant(Q). Injectivity
of the constant coordinate hom gives equality on precisely Q.

## For the actual signed place, not an auxiliary chosen lift

SelectedResidueSinglePoint pins the root of the original signed
Gaussian generator a+bi and the same given w. The actual
ChosenPlaceLift.chosenEmbedding and chosenEmbedding_i identify
its image with residue V (integralOverI w) in the literal K.
The strict actual_residue_char provides characteristic p there.
Strict ActualPointFrob.residue_arithmetic_frob_apply identifies
the actual residual arithmetic ring map with Frobenius on K
by a pointwise equality of ring homs (not on just prime-field
coefficients). Thus the selected residue comparison provided by
the final theorem matches hSamePointResidual on the same P,w in
the separate LocalPrimitiveNorm33. This comparison needs no
torsion or primitivity hypotheses; they are only required later
for lifting and for its norm interpretation.

No derivative, normalization, phase, generic-identity producer,
Weber subfield, or norm adapter is imported. The core and actual
place endpoint are two independent diagnostic source plans,
not an attached CI request. No Lean or remote action was taken.
