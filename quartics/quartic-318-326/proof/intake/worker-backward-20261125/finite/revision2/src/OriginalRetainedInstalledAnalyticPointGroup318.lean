module

public import OriginalRetainedEuclideanGroupMultiplication318
public import OriginalRetainedActualAtlasHausdorff318
public import OriginalRetainedAffineMapContinuity318
public import OriginalRetainedF33ExponentialQuotient318

@[expose] public section
noncomputable section

namespace OriginalRetainedInstalledAnalyticPointGroup318

open AlgebraicGeometry CategoryTheory
open OriginalRetainedProjectiveAffinePiece318 OriginalRetainedClosedProjectiveEvaluation318
open OriginalRetainedProjectiveAffinePoints318 OriginalRetainedComplexZeroByPasting318
open OriginalRetainedAffineChartPointEquiv318 OriginalRetainedEuclideanAtlas318
open OriginalRetainedEuclideanGroupMultiplication318 OriginalRetainedActualAtlasHausdorff318
open OriginalRetainedAffineMapContinuity318 OriginalRetainedF33ExponentialQuotient318
open scoped CategoryTheory.Obj CategoryTheory.MonObj Topology
attribute [local instance] Over.cartesianMonoidalCategory

variable {κ : Type} [Fintype κ] [DecidableEq κ]
variable {A Y : Scheme} (a : A ⟶ Y) [GrpObj (Over.mk a)]
variable {E : Type} [Field E] (σ : E→+*ℂ) (P33 : Spec (CommRingCat.of E) ⟶ Y)
local notation "F" => fiber a (specOf σ≫P33)
local notation "P" => Points a σ P33
local notation "X" => F.left
variable (embedding : X ⟶ Ambient κ) (C : ∀ i, Chart a P33 (specOf σ) embedding i)
local instance chosenTopology : TopologicalSpace P := euclidean a P33 (specOf σ) embedding C

local notation "addrₐ" => (fun i => OriginalRetainedAffineChartPointEquiv318.evaluate
  a P33 (specOf σ) embedding (C i))

def inverseChart (i : κ) : quotientSpec i (C i).I ⟶ X :=
  (C i).j ≫ (GrpObj.inv (X:=F)).left

theorem inverseChart_base (i : κ) :
    inverseChart a σ P33 embedding C i≫F.hom=Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (Poly κ i ⧸ (C i).I))) := by
  rw [inverseChart,Category.assoc,(GrpObj.inv (X:=F)).w]
  exact chosen_chart_base a P33 (specOf σ) embedding (C i)

theorem chart_inverse_exact (i : κ) (r : Rows (C i).I) :
    mapped a P33 (specOf σ) (inverseChart a σ P33 embedding C i)
      (inverseChart_base a σ P33 embedding C i) (evalRow (C i).I) r =
      (addrₐ i r)⁻¹ := by
  apply Over.OverMorphism.ext
  change (Spec.map (CommRingCat.ofHom (evalRow (C i).I r).toRingHom)≫
    ((C i).j≫(GrpObj.inv (X:=F)).left)) =
    (addrₐ i r).left≫(GrpObj.inv (X:=F)).left
  rw [evaluate_left,Category.assoc]

/-- The installed inverse is continuous by its literal affine
restrictions, with no appeal to surjectivity of an exponential or to
a pre-existing topology on an analytic replacement group. -/
theorem original_inv_continuous : Continuous (fun x : P => x⁻¹) := by
  apply continuous_def.2
  intro U Uo
  apply (open_iff a P33 (specOf σ) embedding C _).2
  intro i
  let f := mapped a P33 (specOf σ) (inverseChart a σ P33 embedding C i)
    (inverseChart_base a σ P33 embedding C i) (evalRow (C i).I)
  have same : (fun x : Rows (C i).I => (addrₐ i x)⁻¹)=f :=
    funext (fun x => (chart_inverse_exact a σ P33 embedding C i x).symm)
  change IsOpen ((fun x : Rows (C i).I => (addrₐ i x)⁻¹) ⁻¹' U)
  rw [same]
  exact (mapped_continuous a P33 (specOf σ) embedding C
    (inverseChart a σ P33 embedding C i) (inverseChart_base a σ P33 embedding C i)
    (evalRow (C i).I) (polynomial_of_readRow (C i).I)).isOpen_preimage _ Uo

/-- Build the two topological group operations on the exact installed
origin/group of the one selected A33, with the R244 topology. -/
theorem actualTopologicalGroup : IsTopologicalGroup P where
  continuous_mul := original_mul_continuous a P33 (specOf σ) embedding C
  continuous_inv := original_inv_continuous a σ P33 embedding C

theorem actual_compact_hausdorff_group :
    CompactSpace P ∧ T2Space P ∧ IsTopologicalGroup P :=
  ⟨actual_compact a P33 (specOf σ) embedding C,
    actual_hausdorff a P33 (specOf σ) embedding C,actualTopologicalGroup a σ P33 embedding C⟩

end OriginalRetainedInstalledAnalyticPointGroup318
