module
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section
noncomputable section

namespace OriginalSameJRelativePrincipalGraphBaseChange318

open Algebra
open scoped TensorProduct
universe u v w

variable {A : Type u} {B : Type v}
  [CommRing A] [CommRing B] [Algebra A B]
variable (g : B →ₐ[A] A) (c : B)
variable (hk : RingHom.ker g.toRingHom = Ideal.span (Set.singleton c))
variable (hr : ∀ b : B, b*c=0 → b=0)

abbrev into : A →ₗ[A] B := Algebra.linearMap A B
abbrev mult : B →ₗ[A] B := LinearMap.mulRight A c

include hk in
theorem c_vanishes : g c=0 := by
  have h : c ∈ RingHom.ker g.toRingHom := by
    rw [hk]
    exact Ideal.mem_span_singleton_self c
  exact RingHom.mem_ker.mp h

include hr in
theorem cancel {b d : B} (h : b*c=d*c) : b=d := by
  apply sub_eq_zero.mp
  exact hr (b-d) (by rw [sub_mul,h,sub_self])

include hk in
theorem division (b : B) : ∃ a : B, a*c = b - into (A:=A) (B:=B) (g b) := by
  have hm : b - into (A:=A) (B:=B) (g b) ∈ Ideal.span (Set.singleton c) := by
    rw [← hk]
    apply RingHom.mem_ker.mpr
    change g (b - algebraMap A B (g b)) = 0
    simp only [map_sub,g.commutes,Algebra.algebraMap_self_apply,sub_self]
  exact Ideal.mem_span_singleton'.mp hm

abbrev quot (b : B) : B := Classical.choose (division g c hk b)

theorem quot_eq (b : B) :
    quot g c hk b*c = b-into (A:=A) (B:=B) (g b) :=
  Classical.choose_spec (division g c hk b)

/-- Division is taken in the actual ideal of the graph, after removing
the canonical image of its value on the parameter ring. -/
def proj : B →ₗ[A] B where
  toFun := quot g c hk
  map_add' a b := by
    apply cancel c hr
    change quot g c hk (a+b)*c = (quot g c hk a+quot g c hk b)*c
    simp only [add_mul,quot_eq,map_add]
    exact add_sub_add_comm _ _ _ _
  map_smul' a b := by
    apply cancel c hr
    change quot g c hk (a • b)*c = (a • quot g c hk b)*c
    simp only [quot_eq,smul_mul_assoc,map_smul,smul_sub]

theorem left_split :
    (proj g c hk hr).comp (mult c) = LinearMap.id := by
  apply LinearMap.ext
  intro b
  change quot g c hk (b*c) = b
  apply cancel c hr
  rw [quot_eq,map_mul,c_vanishes g c hk,mul_zero,map_zero,sub_zero]

theorem split_identity :
    (mult c).comp (proj g c hk hr) +
      (into (A:=A) (B:=B)).comp g.toLinearMap = LinearMap.id := by
  apply LinearMap.ext
  intro b
  change quot g c hk b*c + into (g b) = b
  rw [quot_eq,sub_add_cancel]

variable (T : Type w) [CommRing T] [Algebra A T]

abbrev mappedEval : T⊗[A]B →ₐ[A] T⊗[A]A :=
  Algebra.TensorProduct.map (AlgHom.id A T) g

abbrev mappedC : T⊗[A]B := (1:T)⊗ₜ[A]c

theorem mapped_divisor (q : T⊗[A]B) :
    (mult c).lTensor T q = q*mappedC c T := by
  induction q using TensorProduct.induction_on with
  | zero => rw [map_zero,zero_mul]
  | tmul t b =>
    simp only [LinearMap.lTensor_tmul,LinearMap.mulRight_apply,mappedC,
      Algebra.TensorProduct.tmul_mul_tmul,mul_one]
  | add a b ha hb => rw [map_add,add_mul,ha,hb]

theorem mapped_eval_linear :
    (mappedEval g T).toLinearMap = g.toLinearMap.lTensor T := by
  apply TensorProduct.ext'
  intro t b
  simp only [mappedEval,AlgHom.toLinearMap_apply,Algebra.TensorProduct.map_tmul,
    AlgHom.id_apply,LinearMap.lTensor_tmul]

/-- The original whole graph ideal remains a regular principal ideal
after EVERY parameter algebra, including nonflat and nonreduced tests.
The splitting uses the same structural ring map A → B, not a selected
point or a different component. -/
theorem arbitrary_base :
    RingHom.ker (mappedEval g T).toRingHom = Ideal.span (Set.singleton (mappedC c T)) ∧
    ∀ q : T⊗[A]B, q*mappedC c T=0 → q=0 := by
  have L := congrArg (fun h : B →ₗ[A] B => h.lTensor T) (left_split g c hk hr)
  rw [LinearMap.lTensor_comp,LinearMap.lTensor_id] at L
  have LR := congrArg (fun h : B →ₗ[A] B => h.lTensor T) (split_identity g c hk hr)
  rw [LinearMap.lTensor_add,LinearMap.lTensor_comp,LinearMap.lTensor_comp,
    LinearMap.lTensor_id] at LR
  constructor
  · ext q
    rw [RingHom.mem_ker,Ideal.mem_span_singleton']
    constructor
    · intro h
      refine ⟨(proj g c hk hr).lTensor T q,?_⟩
      have read := LinearMap.congr_fun LR q
      change (mult c).lTensor T ((proj g c hk hr).lTensor T q) +
        (into (A:=A) (B:=B)).lTensor T (g.toLinearMap.lTensor T q)=q at read
      have hg0 : g.toLinearMap.lTensor T q = 0 := by
        rw [← mapped_eval_linear g T]
        exact h
      rw [hg0,map_zero,add_zero,mapped_divisor] at read
      exact read
    · rintro ⟨r,rfl⟩
      change mappedEval g T (r*mappedC c T)=0
      rw [map_mul]
      have hc : mappedEval g T (mappedC c T)=0 := by
        simp only [mappedEval,mappedC,Algebra.TensorProduct.map_tmul,AlgHom.id_apply,
          c_vanishes g c hk,TensorProduct.tmul_zero]
      rw [hc,mul_zero]
  · intro q hq
    have key := LinearMap.congr_fun L q
    change (proj g c hk hr).lTensor T ((mult c).lTensor T q)=q at key
    rw [mapped_divisor,hq,map_zero] at key
    exact key.symm

end OriginalSameJRelativePrincipalGraphBaseChange318

#print axioms OriginalSameJRelativePrincipalGraphBaseChange318.left_split
#print axioms OriginalSameJRelativePrincipalGraphBaseChange318.split_identity
#print axioms OriginalSameJRelativePrincipalGraphBaseChange318.arbitrary_base
