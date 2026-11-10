module
public import InjectiveMayerVietorisComparison318
public section
noncomputable section
namespace OriginalHOneCoverIndependence318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalStructureInjectivePresentation318 InjectiveCoverCocycle318
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} (U V : X.Opens)
    {t : (Q X).obj.obj (op ⊤)} (a : Lifts X (TwoOpenAdditiveCocycle318.opens U V) t)
/-- The complete extracted two-cover cocycle is the original signed two-cover
cocycle of its forward coefficient, not merely an equality on one edge. -/
lemma two_cocycle : cocycle a = TwoOpenAdditiveCocycle318.cocycle U V (coefficient a false true) := by
  apply AdditiveCocycleComposition318.ext
  intro i j
  cases i <;> cases j
  · simpa only [TwoOpenAdditiveCocycle318.cocycle, TwoOpenAdditiveCocycle318.transition,
      ↓reduceDIte] using (cocycle a).diagonal false
  · exact (TwoOpenAdditiveCocycle318.forward U V (coefficient a false true)).symm
  · change coefficient a true false = InfinitesimalUnitCocycle318.restrict X
      (TwoOpenAdditiveCocycle318.pair_le U V true false (by decide)) (-coefficient a false true)
    apply AdditiveSheafSections318.app_injective (inclusion X) (V ⊓ U)
    have hf := coefficient_spec a true false
    have hb := coefficient_spec a false true
    simp only [TwoOpenAdditiveCocycle318.opens] at hf hb
    rw [hf, inclusion_restrict, map_neg, hb]
    simp only [difference, TwoOpenAdditiveCocycle318.opens,
      map_neg, map_sub, AdditiveSheafSections318.res_res]
    abel
  · simpa only [TwoOpenAdditiveCocycle318.cocycle, TwoOpenAdditiveCocycle318.transition,
      ↓reduceDIte] using (cocycle a).diagonal true
variable {R : Type} [CommRing R] [IsIntegral X] (p : X ⟶ DualNumberScheme318.base R)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (h : U ⊔ V = ⊤)
/-- Identity of the unchanged original H1-to-pointed map with the construction
from actual injective local lifts. The exact short-complex square fixes the sign. -/
lemma map_from_lifts :
    AffineHOnePointedDeformation318.map p U V hU hV h (boundary X t) =
    InjectiveCoverPointed318.pointed p (TwoOpenAdditiveCocycle318.opens U V)
      (TwoOpenAdditiveCocycle318.cover U V h) a := by
  rw [← InjectiveMayerVietorisComparison318.boundary_coefficient U V h a,
    AffineHOnePointedDeformation318.map_boundary]
  exact congrArg (fun c => AdditiveDeformationClasses318.dualNumberClasses p
    (AffineHOnePointedDeformation318.thickOpens p U V)
    (AffineHOnePointedDeformation318.thick_cover p U V h)
    (AdditiveCocycleRefinement318.classes (CategoryTheory.Limits.pullback.fst p (DualNumberScheme318.structureMap R))
      (TwoOpenAdditiveCocycle318.opens U V) (AffineHOnePointedDeformation318.thickOpens p U V)
      (fun _ => le_rfl) (Quotient.mk _ c))) (two_cocycle U V a).symm
/-- The ORIGINAL map is independent of two-affine-cover choice. The proof uses
all members of the common cover and original derived H1, with no assumed
Čech classification, no affine-intersection premise and no replacement map. -/
lemma independent (W Z : X.Opens) (hW : IsAffineOpen W) (hZ : IsAffineOpen Z)
    (hWZ : W ⊔ Z = ⊤) (z : SheafCohomologyRetraction318.structureH X 1) :
    AffineHOnePointedDeformation318.map p U V hU hV h z =
      AffineHOnePointedDeformation318.map p W Z hW hZ hWZ z := by
  obtain ⟨t,rfl⟩ := boundary_surjective X z
  let a := affine (TwoOpenAdditiveCocycle318.opens U V) (fun i => by cases i; exact hU; exact hV) t
  let b := affine (TwoOpenAdditiveCocycle318.opens W Z) (fun i => by cases i; exact hW; exact hZ) t
  calc
    _ = InjectiveCoverPointed318.pointed p (TwoOpenAdditiveCocycle318.opens U V)
        (TwoOpenAdditiveCocycle318.cover U V h) a := map_from_lifts U V a p hU hV h
    _ = InjectiveCoverPointed318.pointed p (TwoOpenAdditiveCocycle318.opens W Z)
        (TwoOpenAdditiveCocycle318.cover W Z hWZ) b :=
      InjectiveCoverPointed318.common_cover p (TwoOpenAdditiveCocycle318.opens U V)
        (TwoOpenAdditiveCocycle318.cover U V h) (TwoOpenAdditiveCocycle318.opens W Z)
        (TwoOpenAdditiveCocycle318.cover W Z hWZ) a b rfl
    _ = _ := (map_from_lifts W Z b p hW hZ hWZ).symm
end OriginalHOneCoverIndependence318
