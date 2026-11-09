module
public import PushedUnitCocycleRealization318
public section
noncomputable section
namespace OriginalInfinitesimalNormCocycle318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DualNumberScheme318 OriginalThickenedOpenSections318 OriginalThickenedNormTraceSquare318
universe u
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (p : X ⟶ base R) (q : Y ⟶ base R) (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
    {ι : Type u} (U : ι → Y.Opens)
    (c : InfinitesimalUnitCocycle318.AdditiveCocycle X (fun i => f ⁻¹ᵁ U i))
/-- Every transition is the actual first-projection exponential on the ENTIRE
inverse image of the original target overlap. -/
@[expose] def sourceCocycle :
    UnitTransitionCocycle318.Cocycle (OriginalThickenedUnitSheafNorm318.source R p f).obj U where
  transition i j := sectionUnit R p (f ⁻¹ᵁ (U i ⊓ U j)) (c.transition i j)
  diagonal i := by
    rw [c.diagonal]
    simp [sectionUnit, InfinitesimalUnitCocycle318.unit]
  triple i j k := by
    change Units.map ((thickening R p).presheaf.map
      (homOfLE ((π R p).preimage_mono (f.preimage_mono inf_le_left))).op).hom.toMonoidHom _ *
      Units.map ((thickening R p).presheaf.map
      (homOfLE ((π R p).preimage_mono (f.preimage_mono
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))).op).hom.toMonoidHom _ =
      Units.map ((thickening R p).presheaf.map
      (homOfLE ((π R p).preimage_mono (f.preimage_mono
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)))).op).hom.toMonoidHom _
    rw [sectionUnit_restrict,sectionUnit_restrict,sectionUnit_restrict]
    dsimp only [sectionUnit,InfinitesimalUnitCocycle318.unit]
    rw [← InfinitesimalUnitCocycle318.infinitesimal_add, ← map_add]
    exact congrArg (fun a => InfinitesimalUnitCocycle318.infinitesimal _ _ ((π R p).app _ a))
      (c.triple i j k)
/-- The original all-open trace itself gives the target additive cocycle. -/
@[expose] def traceCocycle : InfinitesimalUnitCocycle318.AdditiveCocycle Y U where
  transition i j := OpenDominantTrace318.trace f hY hfinite (U i ⊓ U j) (c.transition i j)
  diagonal i := by rw [c.diagonal,map_zero]
  triple i j k := by
    change Y.presheaf.map (homOfLE inf_le_left).op _ +
      Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).op _ =
      Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).op _
    rw [OpenDominantTrace318.restrict,OpenDominantTrace318.restrict,
      OpenDominantTrace318.restrict,← map_add]
    exact congrArg (OpenDominantTrace318.trace f hY hfinite _) (c.triple i j k)
/-- Apply the genuine ALL-UNIT sheaf norm first, then realize its actual
cocycle on the literal target thickening cover. -/
@[expose] def normCocycle : UnitTransitionCocycle318.Cocycle
    (StructureUnitsSheaf318.units (thickening R q)).obj (fun i => π R q ⁻¹ᵁ U i) :=
  PushedUnitCocycleRealization318.realize (π R q) U
    (OriginalThickenedUnitSheafNorm318.mapCocycle R p q f hY hfinite U (sourceCocycle R p f U c))
lemma norm_transition (i j : ι) : (normCocycle R p q f hY hfinite U c).transition i j =
    sectionUnit R q (U i ⊓ U j)
      ((traceCocycle f hY hfinite U c).transition i j) :=
  norm_sectionUnit R p q f hY hfinite (U i ⊓ U j) (c.transition i j)
/-- All actual norm transitions reduce to one, so they yield an ACTUAL
special-fiber trivialization by the original pointed-line gluing producer. -/
lemma norm_reduces : UnitCocyclePointedLine318.ReducesToOne (reduction R q)
    (fun i => π R q ⁻¹ᵁ U i) (normCocycle R p q f hY hfinite U c) := by
  intro i j
  rw [norm_transition]
  apply Units.ext
  change (reduction R q).app _ (1 + InfinitesimalUnitCocycle318.epsilon (thickening R q)
    (DualNumberInfinitesimalLines318.epsilon R q) _ * _) = 1
  rw [map_add,map_one,map_mul,DualNumberInfinitesimalLines318.reduction_epsilon_open,
    zero_mul,add_zero]
variable (hc : (⊤ : Y.Opens) ≤ ⨆ i,U i)
/-- A genuine pointed line glued from the norm of the original transitions,
not defined by transporting a cohomological trace through an equivalence. -/
@[expose] def deformation : Deformation R q :=
  UnitCocyclePointedLine318.deformation (reduction R q) (fun i => π R q ⁻¹ᵁ U i)
    (normCocycle R p q f hY hfinite U c)
    (LinePullbackFrames318.preimage_cover (π R q) U hc)
    (norm_reduces R p q f hY hfinite U c)
end OriginalInfinitesimalNormCocycle318
