module
public import FirstProjectionCocycleSquare318
public import RefinedSchemeBoundary318
public section
noncomputable section
namespace AffineHOnePointedNaturality318
open AlgebraicGeometry CategoryTheory
open DualNumberScheme318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) (hf : f ≫ q = p)
    (U V : Y.Opens) (W Z : X.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (hZ : IsAffineOpen Z)
    (hUV : U ⊔ V = ⊤) (hWZ : W ⊔ Z = ⊤)
    (hw : W ≤ f ⁻¹ᵁ U) (hz : Z ≤ f ⁻¹ᵁ V)
/-- The ORIGINAL global cohomology pullback and ORIGINAL pointed line pullback
commute under the constructed H1-to-deformation maps whenever the actual two
source charts refine the actual target charts. No abstract tangent map is used. -/
lemma naturality (z : SheafCohomologyRetraction318.structureH Y 1) :
    DualNumberScheme318.pullback R p q f hf (AffineHOnePointedDeformation318.map q U V hU hV hUV z) =
      AffineHOnePointedDeformation318.map p W Z hW hZ hWZ (SchemeSourceCohomology318.pullback f 1 z) := by
  obtain ⟨x,rfl⟩ := AffineCoverHOnePresentation318.boundary_surjective U V hU hV hUV z
  rw [AffineHOnePointedDeformation318.map_boundary]
  have hb := RefinedSchemeBoundary318.pullback_boundary f U V hUV W Z hWZ hw hz x
  change SchemeSourceCohomology318.pullback f 1 (AffineCoverHOnePresentation318.boundary U V hUV x) =
    AffineCoverHOnePresentation318.boundary W Z hWZ
      (f.appLE (U ⊓ V) (W ⊓ Z) (inf_le_inf hw hz) x) at hb
  rw [hb, AffineHOnePointedDeformation318.map_boundary]
  exact FirstProjectionCocycleSquare318.representative_naturality p q f hf U V W Z hw hz hUV hWZ x
end AffineHOnePointedNaturality318
