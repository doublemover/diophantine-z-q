module
public import ComplexLegendreMatrixTransport318
public import PELOriginalOrderedCharacterCoordinate318
public import Mathlib.Analysis.Complex.Polynomial.Basic
public section
noncomputable section
namespace PELOriginalOrderedMatrixTransport318
open scoped OnePoint
open ComplexSphereFourPointNormalization318 ComplexSphereMatrixRealization318
open ComplexLegendreMatrixTransport318
open PELOriginalOrderedCharacterCoordinate318

/-- Actual composition of the three normalizations. The original sphere
map cancels as a map, rather than replacing the actual source curve. -/
@[expose] def matrixChange (i:Fin 4) : Realization (oldToNew i) := by
  let A:=fourPoints (PELOriginalFourBranchCoordinate318.sphereBranches i)
    (PELOriginalFourBranchCoordinate318.sphereBranches_injective i)
  let B:=fourPoints PELOriginalManuscriptNormalization318.points
    PELOriginalManuscriptNormalization318.points_injective
  let C:=fourPoints (points i) (points_injective i)
  have he : ((normalization (PELOriginalFourBranchCoordinate318.sphereBranches i)
      (PELOriginalFourBranchCoordinate318.sphereBranches_injective i)).symm.trans
      (normalization PELOriginalManuscriptNormalization318.points
        PELOriginalManuscriptNormalization318.points_injective)).trans
      (normalization (points i) (points_injective i))=oldToNew i:=by
    ext p
    simp [oldToNew,coordinate,PELOriginalFourBranchCoordinate318.coordinate,
      PELOriginalManuscriptNormalization318.coordinate]
  exact he ▸ compose (compose (inverse A) B) C

lemma branch_change (i j:Fin 4) :
    oldToNew i (branch (PELOriginalFourBranchCoordinate318.branchParameter i)
      (oldOrder i j))=branch (parameter i) j := by
  have hOld:=congrFun (PELOriginalFourBranchCoordinate318.original_values i) (oldOrder i j)
  have hNew:=congrFun (branch_values i) j
  change oldToNew i _=_
  rw [←hOld,oldOrder_exact]
  change coordinate i ((PELOriginalFourBranchCoordinate318.coordinate i).symm
    (PELOriginalFourBranchCoordinate318.coordinate i (branches i j).val))=_
  rw [Homeomorph.symm_apply_apply]
  exact hNew

theorem actual_homogeneous (i:Fin 4) :
    ∃K:ℂ,K≠0 ∧ ∀v:ℂ×ℂ,
      quartic (parameter i) (ComplexProjectiveCrossRatio318.matrix
        (matrixChange i).a (matrixChange i).b (matrixChange i).c (matrixChange i).d v)=
      K*quartic (PELOriginalFourBranchCoordinate318.branchParameter i) v :=
  homogeneous_transport (matrixChange i) _ _ (oldOrder i) (branch_change i)

@[expose] def multiplier (i:Fin 4) : ℂ:=(actual_homogeneous i).choose
lemma multiplier_ne (i:Fin 4) : multiplier i≠0:=(actual_homogeneous i).choose_spec.1
lemma multiplier_spec (i:Fin 4) (v:ℂ×ℂ) :
    quartic (parameter i) (ComplexProjectiveCrossRatio318.matrix
      (matrixChange i).a (matrixChange i).b (matrixChange i).c (matrixChange i).d v)=
    multiplier i*quartic (PELOriginalFourBranchCoordinate318.branchParameter i) v:=
  (actual_homogeneous i).choose_spec.2 v

@[expose] def ordinateScale (i:Fin 4) : ℂ:=(IsAlgClosed.exists_pow_nat_eq (multiplier i) (by decide : 0<2)).choose
lemma ordinateScale_sq (i:Fin 4) : ordinateScale i^2=multiplier i:=
  (IsAlgClosed.exists_pow_nat_eq (multiplier i) (by decide : 0<2)).choose_spec
lemma ordinateScale_ne (i:Fin 4) : ordinateScale i≠0:=by
  intro h
  have hh:=ordinateScale_sq i
  rw [h,zero_pow (by decide : 2≠0)] at hh
  exact multiplier_ne i hh.symm

@[expose] def ordinate (i:Fin 4) (z y:ℂ) : ℂ:=
  ordinateScale i*y/((matrixChange i).c*z+(matrixChange i).d)^2

/-- Exact finite old-to-ordered transport over the SAME original base.
Finiteness of its actual target proves the denominator condition. -/
theorem actual_finite_transport (i:Fin 4) (z w y:ℂ)
    (h:oldToNew i (z:OnePoint ℂ)=(w:OnePoint ℂ))
    (hy:y^2=cubic (PELOriginalFourBranchCoordinate318.branchParameter i) z) :
    (matrixChange i).c*z+(matrixChange i).d≠0 ∧
      ordinate i z y^2=cubic (parameter i) w := by
  obtain ⟨hd,hw⟩:=(matrixChange i).finite_value z w h
  refine ⟨hd,?_⟩
  rw [hw]
  exact ordinate_square _ _ _ _ _ _ _ _ _ _ hd (ordinateScale_sq i) hy
    (multiplier_spec i (z,1))
lemma ordinate_sign (i:Fin 4) (z y:ℂ) : ordinate i z (-y)= -ordinate i z y:=by
  unfold ordinate
  ring
end PELOriginalOrderedMatrixTransport318
