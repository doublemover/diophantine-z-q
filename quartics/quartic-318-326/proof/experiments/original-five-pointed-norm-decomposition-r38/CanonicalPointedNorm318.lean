module
public import OriginalPointedNormTrace318
public import OriginalFiveHOneNormMatrices318
public section
noncomputable section
namespace CanonicalPointedNorm318
open AlgebraicGeometry CategoryTheory
open DualNumberScheme318 AffineHOnePointedDeformation318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
    (U V : Y.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : IsAffineOpen (U ⊓ V)) (hc : U ⊔ V = ⊤) (hf : f ≫ q = p)
    (W Z : X.Opens) (hW : IsAffineOpen W) (hZ : IsAffineOpen Z) (hWZ : W ⊔ Z = ⊤)
/-- The SAME actual norm acts through ANY original source affine cover.
This is the exact common-source join needed by the original five quotients. -/
lemma on_source_cover (z : SheafCohomologyRetraction318.structureH X 1) :
    OriginalPointedNormTrace318.norm p q f hY hfinite U V hU hV hUV hc hf
      (AffineHOnePointedDeformation318.map p W Z hW hZ hWZ z) =
    AffineHOnePointedDeformation318.map q U V hU hV hc
      (AffineHOneComparison318.transfer f (OriginalPointedNormTrace318.traceSheaf f hY hfinite) z) := by
  have he := OriginalHOneCoverIndependence318.independent (f ⁻¹ᵁ U) (f ⁻¹ᵁ V) p
    (hU.preimage f) (hV.preimage f)
    (InverseImageMayerVietoris318.inverseImage_cover f.base U V hc) W Z hW hZ hWZ z
  rw [← he]
  exact OriginalPointedNormTrace318.norm_classification p q f hY hfinite U V hU hV hUV hc hf z
end CanonicalPointedNorm318
