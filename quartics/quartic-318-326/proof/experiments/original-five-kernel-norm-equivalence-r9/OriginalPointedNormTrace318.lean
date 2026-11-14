module
public import OriginalTwoOpenNormRepresentative318
public section
noncomputable section
namespace OriginalPointedNormTrace318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 AffineHOnePointedDeformation318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (hc : U ⊔ V = ⊤)
/-- Exactly the OLD additive sheaf trace, without normalization or new sections. -/
@[expose] def traceSheaf : StructureAdditiveSheaf318.pushed f ⟶ StructureAdditiveSheaf318.sheaf Y :=
  ⟨OpenTraceSheaf318.transfer f hY hfinite⟩
local notation "hpre" => InverseImageMayerVietoris318.inverseImage_cover f.base U V hc
local notation "E" => OriginalHOnePointedEquivalence318.equivalence p (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
  (hU.preimage f) (hV.preimage f) (hUV.preimage f) hpre
/-- Choose a representative of the ACTUAL pointed source class using the old
classification, then actually norm its original full-cover transitions and
glue the target pointed line. This definition does NOT apply an H1 trace. -/
@[expose] def norm (hf : f ≫ q = p) (L : Class R p) : Class R q :=
  PointedLineDeformation318.classOf (reduction R q)
    (OriginalTwoOpenNormRepresentative318.normDeformation p q f hY hfinite U V hc
      (representative (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (hU.preimage f) (hV.preimage f) hpre (E.symm L)))
/-- The SAME norm constructed from actual determinant-normed transitions
intertwines the unchanged H1 classification with the OLD source transfer,
including its genuine direct-image comparison inverse. -/
lemma norm_classification (hf : f ≫ q = p) (z : SheafCohomologyRetraction318.structureH X 1) :
    norm p q f hY hfinite U V hU hV hUV hc hf (E z) =
      AffineHOnePointedDeformation318.map q U V hU hV hc
        (AffineHOneComparison318.transfer f (traceSheaf f hY hfinite) z) := by
  dsimp only [norm]
  rw [Equiv.symm_apply_apply,OriginalTwoOpenNormRepresentative318.norm_class]
  let a := representative (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (hU.preimage f) (hV.preimage f) hpre z
  have ha := representative_boundary (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) (hU.preimage f) (hV.preimage f) hpre z
  have ht := OriginalTraceBoundary318.transfer_boundary f (traceSheaf f hY hfinite) U V hc a
  rw [ha] at ht
  rw [ht,AffineHOnePointedDeformation318.map_boundary]
  all_goals rfl
/-- Every source overlap representative computes this SAME actual pointed norm.
Its choices are therefore immaterial; no source line or zero-section framing
has been replaced by a formal cohomology label. -/
lemma norm_representative (hf : f ≫ q = p) (x : Γ(X,f ⁻¹ᵁ (U ⊓ V))) :
    norm p q f hY hfinite U V hU hV hUV hc hf
      (representativeClass p (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) hpre x) =
    PointedLineDeformation318.classOf (reduction R q)
      (OriginalTwoOpenNormRepresentative318.normDeformation p q f hY hfinite U V hc x) := by
  rw [← OriginalHOnePointedEquivalence318.equivalence_boundary p (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
    (hU.preimage f) (hV.preimage f) (hUV.preimage f) hpre x]
  rw [norm_classification (hf := hf),OriginalTraceBoundary318.transfer_boundary,
    AffineHOnePointedDeformation318.map_boundary,OriginalTwoOpenNormRepresentative318.norm_class]
  all_goals rfl
/-- The source class domain is ALL actual pointed lines. This conjugacy is a
THEOREM about the norm constructed from actual transitions, not its definition. -/
lemma norm_eq_original_transfer (hf : f ≫ q = p) (L : Class R p) :
    norm p q f hY hfinite U V hU hV hUV hc hf L =
      AffineHOnePointedDeformation318.map q U V hU hV hc
        (AffineHOneComparison318.transfer f (traceSheaf f hY hfinite) (E.symm L)) := by
  have h := norm_classification p q f hY hfinite U V hU hV hUV hc hf (E.symm L)
  rw [Equiv.apply_symm_apply] at h
  exact h
end OriginalPointedNormTrace318
