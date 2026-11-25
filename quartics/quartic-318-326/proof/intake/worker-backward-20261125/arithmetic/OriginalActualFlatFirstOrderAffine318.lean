module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Smooth.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
Split the actual flat first-order affine deformation over its fixed
square-zero direction. Smoothness chooses a section of its reduced
algebra; flatness, not a chosen split isomorphism, yields the exact
nilpotent coefficient.
-/
@[expose] public section

open scoped TensorProduct
open TrivSqZeroExt

namespace OriginalActualFlatFirstOrderAffine318

abbrev Sq (R : Type*) := TrivSqZeroExt R R

def epsilon (R : Type*) [CommRing R] : Sq R := inr (1 : R)

variable (R : Type*) [CommRing R]

def eMul : Sq R →ₗ[Sq R] Sq R where
  toFun x := epsilon R * x
  map_add' x y := mul_add _ _ _
  map_smul' r x := by
    change epsilon R * (r*x) = r * (epsilon R*x)
    ring

theorem eMul_reads (x : Sq R) : eMul R x = inr x.fst := by
  apply TrivSqZeroExt.ext
  · simp [eMul,epsilon]
  · simp [eMul,epsilon,smul_eq_mul]

theorem base_exact : Function.Exact (eMul R) (eMul R) := by
  intro x
  constructor
  · intro z
    have h : x.fst = 0 := by
      rw [eMul_reads] at z
      exact congrArg TrivSqZeroExt.snd z
    refine ⟨inl x.snd,?_⟩
    rw [eMul_reads,fst_inl]
    apply TrivSqZeroExt.ext
    · exact h.symm
    · rfl
  · rintro ⟨y,rfl⟩
    rw [eMul_reads,eMul_reads,fst_inr,inr_zero]

section FlatRead
variable {R} {B : Type*} [CommRing B] [Algebra (Sq R) B]

abbrev actualEps : B := algebraMap (Sq R) B (epsilon R)

theorem epsilon_square : (actualEps (R := R) (B := B))^2 = 0 := by
  rw [← map_pow]
  simp [epsilon,pow_two]

private theorem tensor_reads (t : B ⊗[Sq R] Sq R) :
    (TensorProduct.rid (Sq R) B) ((eMul R).lTensor B t) =
      actualEps (R := R) (B := B) * (TensorProduct.rid (Sq R) B) t := by
  refine TensorProduct.inductionOn (motive := fun z =>
    (TensorProduct.rid (Sq R) B) ((eMul R).lTensor B z) =
      actualEps (R := R) (B := B) * (TensorProduct.rid (Sq R) B) z) t ?_ ?_
  · intro b d
    rw [LinearMap.lTensor_tmul,TensorProduct.rid_tmul,TensorProduct.rid_tmul]
    have read : (eMul R) d = epsilon R * d := rfl
    rw [read]
    exact (mul_smul (epsilon R) d b).trans (Algebra.smul_def (epsilon R) (d • b))
  · intro a b ha hb
    simp only [map_add,ha,hb,mul_add]

/-- On the actual flat chart the annihilator of ε is the image of ε.
This remains true at residue characteristics 2 and 3. -/
theorem flat_exact [Module.Flat (Sq R) B] (b : B) :
    actualEps (R := R) (B := B)*b=0 ↔
      ∃ a : B, actualEps (R := R) (B := B)*a=b := by
  let i := TensorProduct.rid (Sq R) B
  have ex := Module.Flat.lTensor_exact B (base_exact R)
  constructor
  · intro hb
    have hz : (eMul R).lTensor B (i.symm b) = 0 := by
      apply i.injective
      rw [tensor_reads,i.apply_symm_apply,hb,map_zero]
    obtain ⟨t,ht⟩ := (ex (i.symm b)).mp hz
    refine ⟨i t,?_⟩
    exact (tensor_reads t).symm.trans (by rw [ht,i.apply_symm_apply])
  · rintro ⟨a,ha⟩
    rw [←ha,←mul_assoc,←pow_two,epsilon_square,zero_mul]

end FlatRead

section ActualReduction
variable {R} {B C : Type*} [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
variable [Algebra (Sq R) B]
variable (q : B →ₐ[R] C)
variable (hk : RingHom.ker q.toRingHom =
  Ideal.span ({actualEps (R := R) (B := B)} : Set B))

include hk

theorem actual_ann [Module.Flat (Sq R) B] (b : B) :
    actualEps (R := R) (B := B)*b=0 ↔ q b=0 := by
  rw [flat_exact (R := R)]
  have h : q b=0 ↔ actualEps (R := R) (B := B) ∣ b := by
    change b ∈ RingHom.ker q.toRingHom ↔ _
    rw [hk,Ideal.mem_span_singleton]
  rw [h]
  exact ⟨fun ⟨a,ha⟩ => ⟨a,ha.symm⟩,fun ⟨a,ha⟩ => ⟨a,ha.symm⟩⟩

theorem epsilon_reduces :
    q (actualEps (R := R) (B := B)) = 0 := by
  have h : actualEps (R := R) (B := B) ∈ RingHom.ker q.toRingHom := by
    rw [hk]
    exact Ideal.mem_span_singleton_self _
  exact h

theorem ker_nil : IsNilpotent (RingHom.ker q.toRingHom) := by
  refine ⟨2,?_⟩
  rw [hk,Ideal.span_singleton_pow,epsilon_square]
  simp

variable [Algebra.FormallySmooth R C] (hq : Function.Surjective q)

/-- A genuine section of the actual reduction, by formal smoothness. -/
noncomputable def liftConstants : C →ₐ[R] B :=
  Algebra.FormallySmooth.liftOfSurjective (AlgHom.id R C) q hq (ker_nil q hk)

theorem liftConstants_reads (c : C) :
    q (liftConstants q hk hq c)=c :=
  Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id R C) q hq (ker_nil q hk) c

/-- The actual chart trivialization, with ε sent to the originally
specified infinitesimal base coordinate. -/
noncomputable def splitMap : Sq C →ₐ[R] B where
  toFun x := liftConstants q hk hq x.fst +
    actualEps (R := R) (B := B) * liftConstants q hk hq x.snd
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by
    simp only [fst_add,snd_add,map_add,mul_add]
    abel
  map_mul' x y := by
    simp only [fst_mul,snd_mul,op_smul_eq_smul,smul_eq_mul,map_add,map_mul]
    have h := epsilon_square (R := R) (B := B)
    linear_combination -(liftConstants q hk hq x.snd * liftConstants q hk hq y.snd)*h
  commutes' r := by
    rw [TrivSqZeroExt.algebraMap_eq_inl']
    simp

theorem split_reads (x : Sq C) : q (splitMap q hk hq x)=x.fst := by
  change q (liftConstants q hk hq x.fst +
    actualEps (R := R) (B := B)*liftConstants q hk hq x.snd)=x.fst
  simp only [map_add,map_mul,liftConstants_reads,epsilon_reduces q hk,
    zero_mul,add_zero]

theorem split_epsilon : splitMap q hk hq (epsilon C) =
    actualEps (R := R) (B := B) := by
  change liftConstants q hk hq ((epsilon C).fst) +
    actualEps (R := R) (B := B) * liftConstants q hk hq ((epsilon C).snd) = _
  simp [epsilon]

theorem split_bijective [Module.Flat (Sq R) B] : Function.Bijective (splitMap q hk hq) := by
  constructor
  · intro x y he
    have hf : x.fst=y.fst := by
      simpa only [split_reads] using congrArg q he
    have hn : actualEps (R := R) (B := B) *
        (liftConstants q hk hq x.snd-liftConstants q hk hq y.snd)=0 := by
      change liftConstants q hk hq x.fst +
          actualEps (R := R) (B := B)*liftConstants q hk hq x.snd =
        liftConstants q hk hq y.fst +
          actualEps (R := R) (B := B)*liftConstants q hk hq y.snd at he
      rw [hf] at he
      linear_combination he
    apply TrivSqZeroExt.ext hf
    have hq' := (actual_ann q hk _).mp hn
    simpa only [map_sub,liftConstants_reads,sub_eq_zero] using hq'
  · intro b
    have hz : q (b-liftConstants q hk hq (q b))=0 := by
      simp only [map_sub,liftConstants_reads,sub_self]
    have hm : b-liftConstants q hk hq (q b) ∈
        Ideal.span ({actualEps (R := R) (B := B)} : Set B) := by
      rw [← hk]
      exact hz
    obtain ⟨c,hc⟩ := Ideal.mem_span_singleton.mp hm
    have he : actualEps (R := R) (B := B) *
        (liftConstants q hk hq (q c)-c)=0 := (actual_ann q hk _).mpr (by
          simp only [map_sub,liftConstants_reads,sub_self])
    refine ⟨inl (q b)+inr (q c),?_⟩
    change liftConstants q hk hq ((inl (q b)+inr (q c) : Sq C).fst) +
      actualEps (R := R) (B := B) *
        liftConstants q hk hq ((inl (q b)+inr (q c):Sq C).snd) = b
    simp only [fst_add,fst_inl,fst_inr,add_zero,snd_add,snd_inl,snd_inr,zero_add]
    linear_combination he - hc

/-- This is an isomorphism of actual affine algebras, so Spec gives the
actual local deformation chart needed to form the overlap cocycle. -/
noncomputable def splitAffine [Module.Flat (Sq R) B] : Sq C ≃ₐ[R] B :=
  AlgEquiv.ofBijective (splitMap q hk hq) (split_bijective q hk hq)

theorem splitAffine_reads [Module.Flat (Sq R) B] (x : Sq C) : q (splitAffine q hk hq x) = x.fst :=
  split_reads q hk hq x

theorem splitAffine_epsilon [Module.Flat (Sq R) B] :
    splitAffine q hk hq (epsilon C) = actualEps (R := R) (B := B) :=
  split_epsilon q hk hq

end ActualReduction
end OriginalActualFlatFirstOrderAffine318

#print axioms OriginalActualFlatFirstOrderAffine318.base_exact
#print axioms OriginalActualFlatFirstOrderAffine318.actual_ann
#print axioms OriginalActualFlatFirstOrderAffine318.splitAffine_reads
#print axioms OriginalActualFlatFirstOrderAffine318.splitAffine_epsilon
