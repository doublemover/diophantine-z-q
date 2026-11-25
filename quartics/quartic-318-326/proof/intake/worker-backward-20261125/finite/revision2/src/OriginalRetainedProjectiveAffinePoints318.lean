module

public import OriginalRetainedProjectiveAffinePiece318
public import OriginalCyclicDivisorRetainedSchemeRead318
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
noncomputable section

namespace OriginalRetainedProjectiveAffinePoints318

open AlgebraicGeometry CategoryTheory MvPolynomial

variable {κ : Type}
abbrev R (κ : Type) := MvPolynomial κ ℂ
variable (I : Ideal (R κ))
abbrev Q := R κ ⧸ I

/-- These are the actual affine equations pulled back from the
original projective immersion. The chosen ideal is not sampled from
a point or selected by matching numerical residues. -/
def solutionSet : Set (κ→ℂ) :=
  {z | ∀ F∈I, MvPolynomial.aeval z F=0}

abbrev Rows := ↥(solutionSet I)

def evalRow (z : Rows I) : Q I→ₐ[ℂ]ℂ :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval z.val) z.property

def readRow (r : Q I→ₐ[ℂ]ℂ) : κ→ℂ :=
  fun i => r (Ideal.Quotient.mk I (MvPolynomial.X i))

theorem polynomial_of_readRow (r : Q I→ₐ[ℂ]ℂ) :
    r.comp (Ideal.Quotient.mkₐ ℂ I) = MvPolynomial.aeval (readRow I r) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [MvPolynomial.aeval_X]
  rfl

theorem readRow_mem (r : Q I→ₐ[ℂ]ℂ) : readRow I r∈solutionSet I := by
  intro F hF
  have e := DFunLike.congr_fun (polynomial_of_readRow I r) F
  change r (Ideal.Quotient.mk I F) = _ at e
  have hq : Ideal.Quotient.mk I F=0 := (Ideal.Quotient.eq_zero_iff_mem (I:=I)).2 hF
  rw [hq,map_zero] at e
  exact e.symm

theorem evalRow_comp (z : Rows I) :
    (evalRow I z).comp (Ideal.Quotient.mkₐ ℂ I)=MvPolynomial.aeval z.val :=
  Ideal.Quotient.liftₐ_comp I (MvPolynomial.aeval z.val) z.property

theorem evalRow_returns (r : Q I→ₐ[ℂ]ℂ) :
    evalRow I ⟨readRow I r,readRow_mem I r⟩=r := by
  apply Ideal.Quotient.algHom_ext
  exact (evalRow_comp I ⟨readRow I r,readRow_mem I r⟩).trans
    (polynomial_of_readRow I r).symm

theorem readRow_returns (z : Rows I) : readRow I (evalRow I z)=z.val := by
  funext i
  have h := DFunLike.congr_fun (evalRow_comp I z) (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X] at h
  exact h

local notation "T" => Spec (CommRingCat.of ℂ)

section AffineSection
variable {G : Scheme} (base : G⟶T)
variable (J : Spec (CommRingCat.of (Q I))⟶G)
variable (hJ : J≫base=Spec.map (CommRingCat.ofHom (algebraMap ℂ (Q I))))
variable [IsOpenImmersion J]

structure SectionInPiece where
  point : T⟶G
  section_eq : point≫base=𝟙 T
  inside : Set.range point⊆Set.range J

def literalRead (z : SectionInPiece I base J) : Q I→ₐ[ℂ]ℂ :=
  OriginalCyclicDivisorRetainedSchemeRead318.read J z.point z.inside base z.section_eq hJ

theorem literalRead_returns (z : SectionInPiece I base J) :
    Spec.map (CommRingCat.ofHom (literalRead I base J hJ z).toRingHom)≫J=z.point :=
  OriginalCyclicDivisorRetainedSchemeRead318.read_returns J z.point z.inside base z.section_eq hJ

end AffineSection

open OriginalRetainedProjectiveAffinePiece318 (retainedCarrier retainedBase)
variable {A Y E : Scheme} (a : A⟶Y) (P33 : E⟶Y) (σ : T⟶E)
local notation "Aσ" => OriginalRetainedComplexZeroByPasting318.fiber a (σ≫P33)
variable (J : Spec (CommRingCat.of (Q I))⟶retainedCarrier a P33 σ)
variable (hJ : J≫retainedBase a P33 σ=Spec.map (CommRingCat.ofHom (algebraMap ℂ (Q I))))
variable [IsOpenImmersion J]

abbrev PointsInPiece :=
  {z : Over.mk (𝟙 T)⟶Aσ // Set.range z.left⊆Set.range J}

/-- Freeze the structural section once before the affine comorphism.
This is the same entire original Scheme arrow, not a selected value. -/
def selectedSection (z : PointsInPiece I a P33 σ J) :
    SectionInPiece I (retainedBase a P33 σ) J where
  point := z.val.left
  section_eq := show z.val.left≫(Aσ).hom=𝟙 T from Over.w z.val
  inside := z.property

def originalPointRead (z : PointsInPiece I a P33 σ J) : Q I→ₐ[ℂ]ℂ :=
  literalRead I (retainedBase a P33 σ) J hJ (selectedSection I a P33 σ J z)

theorem originalPointRead_returns (z : PointsInPiece I a P33 σ J) :
    Spec.map (CommRingCat.ofHom (originalPointRead I a P33 σ J hJ z).toRingHom)≫J=z.val.left :=
  literalRead_returns I (retainedBase a P33 σ) J hJ (selectedSection I a P33 σ J z)

/-- The true normalized affine row reconstructs the actual whole
complex point, not an independently selected point of the same fibre. -/
theorem actual_point_from_dehomogenized_row (z : PointsInPiece I a P33 σ J) :
    let r := originalPointRead I a P33 σ J hJ z
    let row : Rows I := ⟨readRow I r,readRow_mem I r⟩
    Spec.map (CommRingCat.ofHom (evalRow I row).toRingHom)≫J=z.val.left := by
  dsimp only
  rw [evalRow_returns]
  exact originalPointRead_returns I a P33 σ J hJ z

section TopologicalSlice

theorem eval_continuous (F : R κ) :
    Continuous (fun z : κ→ℂ => MvPolynomial.aeval z F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.aeval_C,Algebra.algebraMap_self_apply] using
      (continuous_const : Continuous (fun _ : κ→ℂ => c))
  | add F G hF hG => simpa only [map_add] using hF.fun_add hG
  | mul_X F i hF =>
      have hX : Continuous (fun z : κ→ℂ => z i) := continuous_apply i
      have hMul : Continuous (fun z : κ→ℂ => MvPolynomial.aeval z F * z i) :=
        continuous_mul.comp₂ hF hX
      simpa only [map_mul,MvPolynomial.aeval_X] using hMul

theorem closed_solution_rows : IsClosed (solutionSet I) := by
  have eq : solutionSet I =
      ⋂ F : R κ, ⋂ _ : F∈I, (fun z : κ→ℂ => MvPolynomial.aeval z F)⁻¹' {0} := by
    ext z
    simp only [solutionSet,Set.mem_ofPred_eq,Set.mem_iInter,Set.mem_preimage,Set.mem_singleton_iff]
  rw [eq]
  exact isClosed_iInter fun F => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (eval_continuous F)

/-- The compact closed dominant-coordinate slice of the same
dehomogenized chart. The missing j-coordinate is exactly 1. -/
theorem compact_slice [Fintype κ] :
    IsCompact (solutionSet I ∩ Metric.closedBall (0 : κ→ℂ) 1) :=
  (isCompact_closedBall (0 : κ→ℂ) 1).of_isClosed_subset
    ((closed_solution_rows I).inter Metric.isClosed_closedBall) Set.inter_subset_right

end TopologicalSlice
end OriginalRetainedProjectiveAffinePoints318
