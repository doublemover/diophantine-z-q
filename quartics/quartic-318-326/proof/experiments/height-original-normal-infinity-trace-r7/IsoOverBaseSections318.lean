module
public import NormalModelComparisonOfFactor318
public section
noncomputable section
namespace IsoOverBaseSections318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y B : Scheme.{u}} (e : X ≅ Y) (p : X ⟶ B) (q : Y ⟶ B)
  (h : e.hom ≫ q=p)

include h in
lemma preimage (U : B.Opens) : e.hom ⁻¹ᵁ (q ⁻¹ᵁ U)=p ⁻¹ᵁ U := by
  rw [←Scheme.Hom.comp_preimage,h]

/-- Transport is the actual pullback on sections along the specified
whole-model isomorphism, followed only by its proved base-open equality. -/
@[expose] def sections (U : B.Opens) : Γ(Y,q ⁻¹ᵁ U) ≃+* Γ(X,p ⁻¹ᵁ U) :=
  (preimage e p q h U) ▸ (asIso (e.hom.app (q ⁻¹ᵁ U))).commRingCatIsoToRingEquiv
end IsoOverBaseSections318
