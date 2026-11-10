module
public import ComplexSphereActualCrossRatio318
public import ComplexLegendreCoordinates318
public import Mathlib.GroupTheory.Perm.Sign
public section
noncomputable section
namespace ComplexSphereUnorderedInvariant318
open scoped OnePoint
open ComplexProjectiveCrossRatio318 ComplexSphereActualCrossRatio318
open ComplexLegendreCoordinates318

@[expose] def core (v : Fin 4 → ℂ × ℂ) : ℂ :=
  (bracket (v 0) (v 2)*bracket (v 1) (v 3))^2-
    (bracket (v 0) (v 2)*bracket (v 1) (v 3))*(bracket (v 0) (v 3)*bracket (v 1) (v 2))+
    (bracket (v 0) (v 3)*bracket (v 1) (v 2))^2
@[expose] def denominator (v : Fin 4 → ℂ × ℂ) : ℂ :=
  bracket (v 0) (v 1)^2*bracket (v 0) (v 2)^2*bracket (v 0) (v 3)^2*
    bracket (v 1) (v 2)^2*bracket (v 1) (v 3)^2*bracket (v 2) (v 3)^2
@[expose] def invariant (v : Fin 4 → ℂ × ℂ) : ℂ :=256*core v^3/denominator v

lemma bracket_sq_flip (u v : ℂ × ℂ) : bracket u v^2=bracket v u^2 := by
  dsimp [bracket]
  ring
lemma core_swap (v : Fin 4 → ℂ × ℂ) (i j : Fin 4) :
    core (fun k=>v (Equiv.swap i j k))=core v := by
  fin_cases i <;> fin_cases j <;> simp [core,Equiv.swap_apply_def,bracket] <;> ring
lemma denominator_swap (v : Fin 4 → ℂ × ℂ) (i j : Fin 4) :
    denominator (fun k=>v (Equiv.swap i j k))=denominator v := by
  have h10:=bracket_sq_flip (v 1) (v 0)
  have h20:=bracket_sq_flip (v 2) (v 0)
  have h30:=bracket_sq_flip (v 3) (v 0)
  have h21:=bracket_sq_flip (v 2) (v 1)
  have h31:=bracket_sq_flip (v 3) (v 1)
  have h32:=bracket_sq_flip (v 3) (v 2)
  fin_cases i <;> fin_cases j <;>
    simp [denominator,Equiv.swap_apply_def,h10,h20,h30,h21,h31,h32] <;> ring
lemma invariant_swap (v : Fin 4 → ℂ × ℂ) (i j : Fin 4) :
    invariant (fun k=>v (Equiv.swap i j k))=invariant v := by
  unfold invariant
  rw [core_swap,denominator_swap]

/-- All 24 branch orderings, with no assumptions about the enumeration
or affine representatives. The proof uses genuine permutation induction. -/
theorem invariant_permutation (v : Fin 4 → ℂ × ℂ) (σ : Equiv.Perm (Fin 4)) :
    invariant (fun i=>v (σ i))=invariant v := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => rfl
  | mul_swap σ i j hij ih =>
    change invariant (fun k=>v (σ (Equiv.swap i j k)))=invariant v
    exact (invariant_swap (fun k=>v (σ k)) i j).trans ih

lemma plucker (v : Fin 4 → ℂ × ℂ) :
    bracket (v 0) (v 2)*bracket (v 1) (v 3)-bracket (v 0) (v 3)*bracket (v 1) (v 2)=
      bracket (v 0) (v 1)*bracket (v 2) (v 3) := by
  dsimp [bracket]
  ring
lemma denominator_factor (v : Fin 4 → ℂ × ℂ) :
    denominator v=(bracket (v 0) (v 2)*bracket (v 1) (v 3))^2*
      (bracket (v 0) (v 3)*bracket (v 1) (v 2))^2*
      ((bracket (v 0) (v 2)*bracket (v 1) (v 3))-
        (bracket (v 0) (v 3)*bracket (v 1) (v 2)))^2 := by
  rw [plucker]
  unfold denominator
  ring

lemma legendre_division (A B : ℂ) (hB : B≠0) :
    legendreJ (A/B)=256*(A^2-A*B+B^2)^3/(A^2*B^2*(A-B)^2) := by
  by_cases hA : A=0
  · subst A
    simp [legendreJ]
  by_cases hAB : A=B
  · subst A
    simp [legendreJ,hB]
  unfold legendreJ
  field_simp [hA,hB,sub_ne_zero.mpr hAB,sub_ne_zero.mpr (Ne.symm hAB)]
  <;> ring

lemma bracket_lift_ne {p q : OnePoint ℂ} (h : p≠q) : bracket (lift p) (lift q)≠0 := by
  induction p using OnePoint.rec with
  | infty =>
    induction q using OnePoint.rec with
    | infty => exact (h rfl).elim
    | coe y => norm_num [lift,bracket]
  | coe x =>
    induction q using OnePoint.rec with
    | infty => norm_num [lift,bracket]
    | coe y =>
      have hxy : x≠y := fun he=>h (congrArg (fun z:ℂ=>(z:OnePoint ℂ)) he)
      simpa [lift,bracket] using sub_ne_zero.mpr hxy

lemma legendre_crossRatio (p : Fin 4 → OnePoint ℂ) (hp : Function.Injective p) :
    legendreJ (crossRatio p)=invariant (fun i=>lift (p i)) := by
  have h03 : p 0≠p 3 := fun h=>by have hh:=hp h; norm_num at hh
  have h12 : p 1≠p 2 := fun h=>by have hh:=hp h; norm_num at hh
  have hB:=mul_ne_zero (bracket_lift_ne h03) (bracket_lift_ne h12)
  unfold crossRatio ratio
  rw [legendre_division _ _ hB]
  unfold invariant core
  rw [denominator_factor]

theorem crossRatio_j_permutation (p : Fin 4 → OnePoint ℂ) (hp : Function.Injective p)
    (σ : Equiv.Perm (Fin 4)) :
    legendreJ (crossRatio (fun i=>p (σ i)))=legendreJ (crossRatio p) := by
  rw [legendre_crossRatio _ (hp.comp σ.injective),legendre_crossRatio _ hp]
  exact invariant_permutation (fun i=>lift (p i)) σ

/-- The actual chosen parameter has the SAME invariant under any
permutation of the original quadruple. Parameters need not be equal. -/
theorem parameter_j_permutation (p : Fin 4 → OnePoint ℂ) (hp : Function.Injective p)
    (σ : Equiv.Perm (Fin 4)) :
    legendreJ (ComplexSphereFourPointNormalization318.parameter
      (fun i=>p (σ i)) (hp.comp σ.injective))=
      legendreJ (ComplexSphereFourPointNormalization318.parameter p hp) := by
  rw [parameter_eq_crossRatio,parameter_eq_crossRatio,
    legendre_crossRatio _ (hp.comp σ.injective),legendre_crossRatio _ hp]
  exact invariant_permutation (fun i=>lift (p i)) σ
end ComplexSphereUnorderedInvariant318
