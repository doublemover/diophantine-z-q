module
public import FourRootDerivativeIdealRegular318
public section
noncomputable section
namespace FourRootEffectiveDerivativeZero318
open AlgebraicGeometry CategoryTheory
open FourRootGluedDerivativeIdeal318 FourRootDerivativeZeroIdeals318
open FourRootDerivativeIdealClosed318
variable (b:Fin 4→ℂ)(hb:Function.Injective b)
/-- At EVERY original scheme point the SAME constructed closed zero
subscheme is the actual quotient by one regular equation on an open
affine neighborhood. This is the scheme-theoretic effective principal
Cartier condition, not a renamed pointwise divisor or its support. -/
theorem regular_quotient_neighborhood(x:FourRootGluedScheme318.scheme b):
    ∃(A:CommRingCat)(j:Spec A⟶FourRootGluedScheme318.scheme b),
      IsOpenImmersion j∧x∈Set.range j∧
      ∃(c:A)(z:Spec (CommRingCat.of (A⧸Ideal.span {c}))⟶zeroScheme b),
        IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {c})))) z j (into b)∧
          ∀a:A,a*c=0→a=0:=by
  rcases FourRootGluedScheme318.charts_cover b x with ⟨q,hq⟩|⟨q,hq⟩
  · refine ⟨CommRingCat.of (FourRootAffineCoordinateRing318.Ring b),
      FourRootGluedScheme318.finiteChart b,inferInstance,⟨q,hq⟩,
      finiteGenerator b,finiteChart b,finite_square b,?_⟩
    letI:IsDomain (FourRootAffineCoordinateRing318.Ring b):=
      FourRootActualGenericField318.affine_domain b hb
    intro a h
    exact (mul_eq_zero.mp h).resolve_right (FourRootDerivativeIdealRegular318.finite_nonzero b hb)
  · refine ⟨CommRingCat.of (FourRootInfinityCoordinateRing318.Ring b),
      FourRootGluedScheme318.infinityChart b,inferInstance,⟨q,hq⟩,
      infinityGenerator b,infinityChart b,infinity_square b,?_⟩
    letI:IsDomain (FourRootInfinityCoordinateRing318.Ring b):=
      FourRootInfinityDomain318.infinity_domain b hb
    intro a h
    exact (mul_eq_zero.mp h).resolve_right (FourRootDerivativeIdealRegular318.infinity_nonzero b hb)
end FourRootEffectiveDerivativeZero318
