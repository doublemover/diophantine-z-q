module
public import NormalizationClosureChart318
public section
noncomputable section
namespace NormalizationClosureChartRange318
open AlgebraicGeometry CategoryTheory
variable {A B : CommRingCat} {Y : Scheme}
  (φ : A ⟶ B) (j : Spec A ⟶ Y) [IsOpenImmersion j]
  (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
  (hf : f=Spec.map φ ≫ j)

/-- The OLD section-equivalence chart covers the whole inverse image of
its base chart. This follows from its construction, not from density. -/
lemma range :
    letI := φ.hom.toAlgebra
    letI := (NormalizationClosureChart318.data φ j f hf).isOpen
    (NormalizationClosureChart318.data φ j f hf).chart.opensRange=
      f.fromNormalization ⁻¹ᵁ (j ''ᵁ ⊤) := by
  letI := φ.hom.toAlgebra
  let e := InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf
  let hU := (NormalizationBaseCompatibility318.target_affine j).preimage f.fromNormalization
  let E := Scheme.Spec.mapIso e.toCommRingCatIso.op
  change (E.hom ≫ hU.fromSpec).opensRange=_
  exact (Scheme.Hom.opensRange_comp_of_isIso _ _).trans hU.opensRange_fromSpec

/-- Transport the exact full chart image across a specified model
isomorphism that commutes with the actual projection. -/
lemma transport {A X Y Z : Scheme} (j : A ⟶ X) [IsOpenImmersion j]
    (e : X ≅ Y) (p : Y ⟶ Z) (q : X ⟶ Z) (h : e.hom ≫ p=q)
    (U : Z.Opens) (hr : j.opensRange=q ⁻¹ᵁ U) :
    (j ≫ e.hom).opensRange=p ⁻¹ᵁ U := by
  rw [Scheme.Hom.opensRange_comp,hr,←h,Scheme.Hom.comp_preimage,
    Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Hom.opensRange_of_isIso,top_inf_eq]
end NormalizationClosureChartRange318
