module
public import ActualGaussianWeberMixedFirstJet318
public import ActualGaussianWeberMixedStockCoordinates318
public section
noncomputable section

namespace ActualGaussianWeberAcceptedMixedFirstJet318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberValuedKernelChart318
open ActualGaussianWeberMixedStockCoordinates318 ActualGaussianWeberMixedValuedData318
open ActualGaussianWeberMixedFirstJet318

variable {F : Type*} [Field F] [DecidableEq F] (V : ValuationSubring F)

/-- First-order refinement of the exact checked mixed addition: the
coordinates used in the conclusion are the stock point coordinates. -/
theorem mixed_abscissa_expansion (h2 : (2:ResidueField V) ≠ 0)
    (P : WP F) (a b s : V)
    (hQ : (curve F).toAffine.Nonsingular (V.subtype a) (V.subtype b))
    (hP : specialize V h2 P=Point.zero) (hs : tCoord P=V.subtype s) :
    ∃ X Y : V, ∃ hR : (curve F).toAffine.Nonsingular (V.subtype X) (V.subtype Y),
      P+Point.some (V.subtype a) (V.subtype b) hQ =
        Point.some (V.subtype X) (V.subtype Y) hR ∧
      ∃ c : V, X=a+(2*b)*s+s^2*c := by
  by_cases hO : P=Point.zero
  · subst P
    have hs0 : s=0 := V.subtype_injective (hs.symm.trans (map_zero V.subtype).symm)
    refine ⟨a,b,hQ,zero_add _,0,?_⟩
    rw [hs0,mul_zero,mul_zero,add_zero,add_zero]
  · obtain ⟨T⟩ := from_kernel V h2 P hP
    obtain ⟨K,hR,hEq⟩ := mixed_stock_coordinates V h2 P a b hQ hP hO T
    have he : T.t=s := V.subtype_injective (T.t_exact.trans hs)
    obtain ⟨c,hc⟩ := mixed_firstJet K.w_relation K.u_inv K.beta_inv (B:=b)
    refine ⟨K.X,K.Y,hR,hEq,c,?_⟩
    rw [K.x_formula,hc,he]

/-- If the actual transported origin parameter is second order, its
mixed abscissa has exactly zero first-order term at the same scale. -/
theorem stationary_mixed_abscissa (h2 : (2:ResidueField V) ≠ 0)
    (P : WP F) (a b t : V)
    (hQ : (curve F).toAffine.Nonsingular (V.subtype a) (V.subtype b))
    (hP : specialize V h2 P=Point.zero)
    (hs : ∃ s : V, tCoord P=V.subtype (t^2*s)) :
    ∃ X Y : V, ∃ hR : (curve F).toAffine.Nonsingular (V.subtype X) (V.subtype Y),
      P+Point.some (V.subtype a) (V.subtype b) hQ =
        Point.some (V.subtype X) (V.subtype Y) hR ∧
      ∃ c : V, X=a+t^2*c := by
  obtain ⟨s,hs⟩ := hs
  obtain ⟨X,Y,hR,hEq,c,hc⟩ := mixed_abscissa_expansion V h2 P a b (t^2*s) hQ hP hs
  exact ⟨X,Y,hR,hEq,2*b*s+t^2*s^2*c,by rw [hc]; ring⟩

end ActualGaussianWeberAcceptedMixedFirstJet318
