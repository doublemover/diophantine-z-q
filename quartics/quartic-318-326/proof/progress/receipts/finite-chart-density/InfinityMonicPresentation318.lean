module
public import InfinityChart318
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.TorsionFree
import all Mathlib.RingTheory.AdjoinRoot
public section
noncomputable section
namespace InfinityMonicPresentation318
open Polynomial
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R:Type u} [CommRing R] (A B:R)

/-- The same infinity equation, monic in x over the full polynomial z-line. -/
@[expose] def polynomial : R[X][X]:=
  X^3+(C (C A*X^2)*X+C (C B*X^3-X))
lemma monic : (polynomial A B).Monic:=by
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (Polynomial.degree_C_mul_X_le _)
    norm_num
  · apply lt_of_le_of_lt Polynomial.degree_C_le
    norm_num
abbrev Model:=AdjoinRoot (polynomial A B)
@[expose] def x:Model A B:=AdjoinRoot.root (polynomial A B)
@[expose] def z:Model A B:=algebraMap R[X] (Model A B) X
lemma relation : z A B-x A B^3-algebraMap R (Model A B) A*x A B*z A B^2-
    algebraMap R (Model A B) B*z A B^3=0:=by
  have h:=AdjoinRoot.eval₂_root (polynomial A B)
  change (polynomial A B).eval₂ (algebraMap R[X] (Model A B)) (x A B)=0 at h
  simp only [polynomial,eval₂_add,eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,
    map_mul,map_pow,map_sub] at h
  have hc (q:R):algebraMap R[X] (Model A B) (C q)=algebraMap R (Model A B) q:=by
    rw [AdjoinRoot.algebraMap_eq' R,Polynomial.algebraMap_eq];rfl
  simp only [hc] at h
  change x A B^3+(algebraMap R (Model A B) A*z A B^2*x A B+
    (algebraMap R (Model A B) B*z A B^3-z A B))=0 at h
  linear_combination -h

@[expose] def forward : InfinityChart318.Ring A B→ₐ[R]Model A B:=
  InfinityChart318.lift A B (x A B) (z A B) (relation A B)
@[simp] lemma forward_x : forward A B (InfinityChart318.x A B)=x A B:=InfinityChart318.lift_x ..
@[simp] lemma forward_z : forward A B (InfinityChart318.z A B)=z A B:=InfinityChart318.lift_z ..

lemma eval_relation : (polynomial A B).eval₂
    (Polynomial.aeval (InfinityChart318.z A B)).toRingHom (InfinityChart318.x A B)=0:=by
  simp only [polynomial,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C]
  change InfinityChart318.x A B^3+
    ((Polynomial.aeval (InfinityChart318.z A B)) (C A*X^2)*InfinityChart318.x A B+
      (Polynomial.aeval (InfinityChart318.z A B)) (C B*X^3-X))=0
  simp only [map_mul,map_pow,map_sub,aeval_C,aeval_X]
  linear_combination -InfinityChart318.relation A B
@[expose] def backward : Model A B→ₐ[R]InfinityChart318.Ring A B:=
  AdjoinRoot.liftAlgHom (polynomial A B) (Polynomial.aeval (InfinityChart318.z A B))
    (InfinityChart318.x A B) (eval_relation A B)
@[simp] lemma backward_x : backward A B (x A B)=InfinityChart318.x A B:=
  AdjoinRoot.liftAlgHom_root ..
@[simp] lemma backward_z : backward A B (z A B)=InfinityChart318.z A B:=by
  simp only [z,backward,AdjoinRoot.algebraMap_eq,AdjoinRoot.liftAlgHom_of,Polynomial.aeval_X]
lemma backward_forward : (backward A B).comp (forward A B)=AlgHom.id R _:=by
  apply InfinityChart318.hom_ext <;> simp
lemma forward_injective : Function.Injective (forward A B):=by
  apply Function.HasLeftInverse.injective
  exact ⟨backward A B,fun t=>congrArg (fun f:InfinityChart318.Ring A B→ₐ[R]InfinityChart318.Ring A B=>f t)
    (backward_forward A B)⟩

/-- The actual infinity denominator is regular even over nonreduced bases. -/
theorem z_regular : InfinityChart318.z A B∈nonZeroDivisors (InfinityChart318.Ring A B):=by
  letI:Module.Free R[X] (Model A B):=(monic A B).free_adjoinRoot
  rw [mem_nonZeroDivisors_iff_left]
  intro t ht
  apply forward_injective A B
  rw [map_zero]
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M:=Model A B)
    (Polynomial.X_mem_nonZeroDivisors (R:=R))
  simp only [Algebra.smul_def]
  change algebraMap R[X] (Model A B) X*forward A B t=algebraMap R[X] (Model A B) X*0
  simpa only [map_mul,forward_z,map_zero,mul_zero,z] using congrArg (forward A B) ht
end InfinityMonicPresentation318
