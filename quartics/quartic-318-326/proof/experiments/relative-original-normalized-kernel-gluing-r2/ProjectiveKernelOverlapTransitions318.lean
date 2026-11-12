module
public import ProjectiveKernelOverlapAlgebras318
public section
noncomputable section
namespace ProjectiveKernelOverlapTransitions318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (R : CommRingCat.{0}) (P Q : Type) [AddCommGroup P] [Module R P]
  [AddCommGroup Q] [Module R Q] [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q] (d : P →ₗ[R] Q)
local notation "F" => FiniteProjectiveEvaluationFrame318.frame R P
local notation "B" => ProjectiveParameterSliceAlgebra318.algebra R P
local notation "O" => ProjectiveParameterSliceLocalization318.algebra R P
local notation "C" => ProjectiveKernelNormalizedAlgebras318.sliceRing R P Q d
local notation "eqn" => ProjectiveKernelEquations318.equation R P Q d
local notation "D" => ProjectiveKernelOverlapAlgebras318.ring R P Q d
local notation "q" => ProjectiveKernelOverlapAlgebras318.quotient R P Q d
local notation "tr" => ProjectiveParameterSliceLocalization318.transition R P
variable (i j : Fin F.size)
/-- Exact change of ALL kernel equations on the actual old overlap. -/
lemma equation_transition (φ : Module.Dual R Q) :
    tr i j (ProjectiveKernelOverlapAlgebras318.equation R P Q d j i φ)=
      (((ProjectiveParameterSliceLocalization318.unit R P i j)⁻¹:(O i j)ˣ):O i j)*
        ProjectiveKernelOverlapAlgebras318.equation R P Q d i j φ := by
  rw [ProjectiveKernelOverlapAlgebras318.equation,ProjectiveParameterSliceLocalization318.transition_point]
  exact ProjectiveParameterUnitAction318.pointScale_generator R P (O i j) _ _ (φ.comp d)
lemma kernel : ProjectiveKernelOverlapAlgebras318.ideal R P Q d j i≤
    RingHom.ker ((q i j).comp (tr i j)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro a ⟨φ,rfl⟩
  change q i j (tr i j (ProjectiveKernelOverlapAlgebras318.equation R P Q d j i φ))=0
  rw [equation_transition,map_mul]
  have hz : q i j (ProjectiveKernelOverlapAlgebras318.equation R P Q d i j φ)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self φ))
  rw [hz,mul_zero]
@[expose] def transition : D j i →ₐ[R] D i j :=
  Ideal.Quotient.liftₐ (ProjectiveKernelOverlapAlgebras318.ideal R P Q d j i)
    ((q i j).comp (tr i j)) (fun a ha => kernel R P Q d i j ha)
lemma transition_quotient : (transition R P Q d i j).comp (q j i)=(q i j).comp (tr i j) :=
  Ideal.Quotient.liftₐ_comp _ _ _
lemma transition_mk (a : O j i) : transition R P Q d i j (q j i a)=q i j (tr i j a) :=
  DFunLike.congr_fun (transition_quotient R P Q d i j) a
/-- The original inverse transition law descends to the full quotient
rings, not just their spectra or residue-field points. -/
lemma transition_comp : (transition R P Q d i j).comp (transition R P Q d j i)=AlgHom.id R (D i j) := by
  apply AlgHom.ext
  intro z
  obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective z
  change transition R P Q d i j (transition R P Q d j i (q i j a))=q i j a
  rw [transition_mk,transition_mk]
  exact congrArg (q i j) (DFunLike.congr_fun (ProjectiveParameterSliceLocalizationIso318.transition_comp R P i j) a)
@[expose] def equivalence : D j i ≃ₐ[R] D i j where
  __ := transition R P Q d i j
  invFun := transition R P Q d j i
  left_inv z := DFunLike.congr_fun (transition_comp R P Q d j i) z
  right_inv z := DFunLike.congr_fun (transition_comp R P Q d i j) z

end ProjectiveKernelOverlapTransitions318
