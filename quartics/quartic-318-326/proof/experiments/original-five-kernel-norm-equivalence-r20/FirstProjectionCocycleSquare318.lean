module
public import TwoOpenCocycleNaturality318
public section
noncomputable section
namespace FirstProjectionCocycleSquare318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits InfinitesimalUnitCocycle318
open DualNumberScheme318 TwoOpenAdditiveCocycle318 AffineHOnePointedDeformation318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type} [CommRing R] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) (hf : f ≫ q = p)
    (U V : Y.Opens) (W Z : X.Opens) (hW : W ≤ f ⁻¹ᵁ U) (hZ : Z ≤ f ⁻¹ᵁ V)
include hW hZ in
/-- Actual first-projection square supplies the required whole thickened chart
containments, without an equality of quotient-map inverse-image opens. -/
lemma thick_refinement (a : Bool) :
    thickOpens p W Z a ≤ map R p q f hf ⁻¹ᵁ thickOpens q U V a := by
  change (pullback.fst p (structureMap R)) ⁻¹ᵁ opens W Z a ≤
    map R p q f hf ⁻¹ᵁ ((pullback.fst q (structureMap R)) ⁻¹ᵁ opens U V a)
  rw [← Scheme.Hom.comp_preimage,
    show map R p q f hf ≫ pullback.fst q (structureMap R) = pullback.fst p (structureMap R) ≫ f from
      RelativeLineFunctorPullback318.baseMap_fst p q f hf (structureMap R), Scheme.Hom.comp_preimage]
  exact (pullback.fst p (structureMap R)).preimage_mono
    (TwoOpenCocycleNaturality318.coverLE f U V W Z hW hZ a)
/-- Original first projections, the original quotient map and actual overlap
coefficient pullback give the SAME complete additive cocycle on the thickening. -/
lemma cocycle_square (x : Γ(Y,U ⊓ V)) :
    AdditiveCocycleRefinement318.cocycle (map R p q f hf) (thickOpens q U V) (thickOpens p W Z)
      (thick_refinement p q f hf U V W Z hW hZ)
      (AdditiveCocycleRefinement318.cocycle (pullback.fst q (structureMap R))
        (opens U V) (thickOpens q U V) (fun _ => le_rfl) (TwoOpenAdditiveCocycle318.cocycle U V x)) =
    AdditiveCocycleRefinement318.cocycle (pullback.fst p (structureMap R))
      (opens W Z) (thickOpens p W Z) (fun _ => le_rfl)
      (TwoOpenAdditiveCocycle318.cocycle W Z (f.appLE (U ⊓ V) (W ⊓ Z) (inf_le_inf hW hZ) x)) := by
  rw [← TwoOpenCocycleNaturality318.cocycle f U V W Z hW hZ x]
  rw [AdditiveCocycleComposition318.comp, AdditiveCocycleComposition318.comp]
  apply AdditiveCocycleComposition318.congr_map
  exact RelativeLineFunctorPullback318.baseMap_fst p q f hf (structureMap R)
variable (hUV : U ⊔ V = ⊤) (hWZ : W ⊔ Z = ⊤)
/-- The original overlap representative's actual pointed line pulls back to the
actual pointed line of the original pulled overlap representative. -/
lemma representative_naturality (x : Γ(Y,U ⊓ V)) :
    DualNumberScheme318.pullback R p q f hf (representativeClass q U V hUV x) =
      representativeClass p W Z hWZ (f.appLE (U ⊓ V) (W ⊓ Z) (inf_le_inf hW hZ) x) := by
  have hh := DualNumberCocycleNaturality318.pointed_cocycle p q f hf
    (thickOpens q U V) (thickOpens p W Z) (thick_cover q U V hUV) (thick_cover p W Z hWZ)
    (thick_refinement p q f hf U V W Z hW hZ)
    (AdditiveCocycleRefinement318.cocycle (pullback.fst q (structureMap R))
      (opens U V) (thickOpens q U V) (fun _ => le_rfl) (TwoOpenAdditiveCocycle318.cocycle U V x))
  rw [cocycle_square p q f hf U V W Z hW hZ x] at hh
  exact hh
end FirstProjectionCocycleSquare318
