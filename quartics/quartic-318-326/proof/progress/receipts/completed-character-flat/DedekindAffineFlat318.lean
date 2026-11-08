module
public import BivariateIntegral318
public import DominantFunctionField318
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace DedekindAffineFlat318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 350000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y)

/-- Actual affine restriction and the original map on its entire section ring. -/
theorem restrict_flat_iff [IsAffineHom f] {U:Y.Opens} (hU:IsAffineOpen U):
    Flat (f∣_U) ↔ (f.app U).hom.Flat:=by
  letI:IsAffine U:=hU
  letI:IsAffine (f⁻¹ᵁU):=hU.preimage f
  rw [HasRingHomProperty.iff_of_isAffine (P:=@Flat)]
  change ((f∣_U).app ⊤).hom.Flat ↔ (f.app U).hom.Flat
  rw [morphismRestrict_app']
  have he : ((f⁻¹ᵁU).ι ''ᵁ ((f∣_U)⁻¹ᵁ⊤))=f⁻¹ᵁU := by
    rw [TopologicalSpace.Opens.map_top,Scheme.Opens.ι_image_top]
  exact (f.appLE_congr _ U.ι_image_top he (fun g => g.hom.Flat)).trans
    (by rw [Scheme.Hom.appLE_eq_app])

/-- Dominance into a Dedekind affine target makes the actual section map flat. -/
theorem app_flat [IsIntegral X] [IsIntegral Y] [IsFinite f] [IsDominant f]
    (U:Y.Opens) [Nonempty U] [IsDedekindDomain Γ(Y,U)]:
    (f.app U).hom.Flat:=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:IsSchemeTheoreticallyDominant f:=IsSchemeTheoreticallyDominant.of_isDominant f
  letI:Algebra Γ(Y,U) Γ(X,f⁻¹ᵁU):=(f.app U).hom.toAlgebra
  exact BivariateIntegral318.flat_of_injective (f.app_injective U)

theorem restrict_flat [IsIntegral X] [IsIntegral Y] [IsFinite f] [IsDominant f]
    (U:Y.Opens) (hU:IsAffineOpen U) [Nonempty U] [IsDedekindDomain Γ(Y,U)]:
    Flat (f∣_U):=(restrict_flat_iff f hU).mpr (app_flat f U)

/-- Transport along the exact section equivalence of an actual open immersion. -/
theorem sections_dedekind (A:CommRingCat.{u}) [IsDedekindDomain A]
    (j:Spec A⟶Y) [IsOpenImmersion j]:IsDedekindDomain Γ(Y,j.opensRange):=by
  let e:A≃+*Γ(Y,j.opensRange):=
    ((Scheme.ΓSpecIso A).symm ≪≫ IsOpenImmersion.ΓIsoTop j).commRingCatIsoToRingEquiv
  letI:IsDomain Γ(Y,j.opensRange):=e.symm.injective.isDomain
  letI:IsNoetherianRing Γ(Y,j.opensRange):=isNoetherianRing_of_ringEquiv A e
  letI:Ring.DimensionLEOne Γ(Y,j.opensRange):=Ring.DimensionLEOne.of_ringEquiv e.symm
  letI:IsIntegrallyClosed Γ(Y,j.opensRange):=IsIntegrallyClosed.of_equiv e
  exact { (inferInstance:IsDomain Γ(Y,j.opensRange)),
    (inferInstance:IsNoetherianRing Γ(Y,j.opensRange)),
    (inferInstance:Ring.DimensionLEOne Γ(Y,j.opensRange)),
    (inferInstance:IsIntegrallyClosed Γ(Y,j.opensRange)) with }

theorem restrict_chart_flat [IsIntegral X] [IsIntegral Y] [IsFinite f] [IsDominant f]
    (A:CommRingCat.{u}) [IsDedekindDomain A]
    (j:Spec A⟶Y) [IsOpenImmersion j] [Nonempty j.opensRange]:Flat (f∣_j.opensRange):=by
  letI:=sections_dedekind A j
  exact restrict_flat f j.opensRange (isAffineOpen_opensRange j)
end DedekindAffineFlat318
