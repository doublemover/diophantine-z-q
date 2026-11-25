module
public import OriginalSameJLiteralAbelDualGraph318
public import Mathlib.RingTheory.TensorProduct.Maps

@[expose] public section
noncomputable section

open Algebra
open scoped TensorProduct

namespace OriginalSameJActualGraphBaseChange318
open OriginalSameJLiteralAbelDualGraph318 (Dual mul_snd graph)
open OriginalSameJRetainedAffineJet318 (Jet)

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]

def coefficients : Dual k →ₐ[k] Dual A where
  toFun x := (algebraMap k A x.fst, algebraMap k A x.snd)
  map_zero' := TrivSqZeroExt.ext (map_zero _) (map_zero _)
  map_one' := TrivSqZeroExt.ext (map_one _) (map_zero _)
  map_add' x y := TrivSqZeroExt.ext (map_add _ _ _) (map_add _ _ _)
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul (algebraMap k A) x.fst y.fst
    · simp only [mul_snd, TrivSqZeroExt.fst_mk, TrivSqZeroExt.snd_mk, map_add, map_mul]
  commutes' x := TrivSqZeroExt.ext rfl (map_zero _)

def intoDual : (A⊗[k]Dual k) →ₐ[A] Dual A :=
  Algebra.TensorProduct.lift (Algebra.ofId A (Dual A)) coefficients (fun _ _ => Commute.all _ _)

theorem tensor_read (a : A) (z : Dual k) :
    intoDual (a⊗ₜ[k]z) =
      ((a * algebraMap k A z.fst, a * algebraMap k A z.snd) : Dual A) := by
  rw [intoDual, Algebra.TensorProduct.lift_tmul]
  apply TrivSqZeroExt.ext
  · rfl
  · change (((a,0) : Dual A) * coefficients z).snd = _
    rw [mul_snd]
    change a * algebraMap k A z.snd + algebraMap k A z.fst * 0 = _
    rw [mul_zero, add_zero]

abbrev epsilon : Dual k := TrivSqZeroExt.inr (1:k)

def firstNil : A →ₗ[A] (A⊗[k]Dual k) :=
  (LinearMap.id : A→ₗ[A]A).smulRight ((1:A)⊗ₜ[k]epsilon)

theorem firstNil_read (a : A) : (firstNil (k:=k)) a = a⊗ₜ[k]epsilon := by
  change a • ((1:A)⊗ₜ[k]epsilon) = _
  rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

theorem firstNil_square (a b : A) : firstNil (k:=k) a * firstNil (k:=k) b = 0 := by
  rw [firstNil_read, firstNil_read, Algebra.TensorProduct.tmul_mul_tmul,
    TrivSqZeroExt.inr_mul_inr, TensorProduct.tmul_zero]

def intoTensor : Dual A →ₐ[A] A⊗[k]Dual k :=
  TrivSqZeroExt.liftEquivOfComm ⟨firstNil (k:=k), firstNil_square⟩

theorem dual_read (x : Dual A) :
    intoTensor (k:=k) x = x.fst⊗ₜ[k](1:Dual k)+x.snd⊗ₜ[k]epsilon := by
  change algebraMap A (A⊗[k]Dual k) x.fst + firstNil (k:=k) x.snd = _
  rw [Algebra.TensorProduct.algebraMap_apply, firstNil_read]

theorem left_inverse :
    Function.LeftInverse (intoTensor (k:=k) (A:=A)) (intoDual (k:=k) (A:=A)) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a z =>
      rw [tensor_read, dual_read]
      change (a * algebraMap k A z.fst)⊗ₜ[k](1:Dual k)+
        (a * algebraMap k A z.snd)⊗ₜ[k](epsilon (k:=k)) = a⊗ₜ[k]z
      have h1 : a * algebraMap k A z.fst = z.fst • a := by
        rw [Algebra.smul_def, mul_comm]
      have h2 : a * algebraMap k A z.snd = z.snd • a := by
        rw [Algebra.smul_def, mul_comm]
      rw [h1, h2, TensorProduct.smul_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_add]
      apply congrArg (fun t : Dual k => a⊗ₜ[k]t)
      apply TrivSqZeroExt.ext
      · change z.fst*1+z.snd*0=z.fst
        rw [mul_one,mul_zero,add_zero]
      · change z.fst*0+z.snd*1=z.snd
        rw [mul_zero,mul_one,zero_add]

theorem right_inverse :
    Function.RightInverse (intoTensor (k:=k) (A:=A)) (intoDual (k:=k) (A:=A)) := by
  intro x
  rw [dual_read,map_add,tensor_read,tensor_read]
  apply TrivSqZeroExt.ext
  · change x.fst*algebraMap k A 1+x.snd*algebraMap k A 0 = x.fst
    rw [map_one,map_zero,mul_one,mul_zero,add_zero]
  · change x.fst*algebraMap k A 0+x.snd*algebraMap k A 1 = x.snd
    rw [map_zero,map_one,mul_zero,mul_one,zero_add]

/-- Literal fibre product algebra, so the graph kernel in Dual A is
the real closed immersion of the section on X×Spec(k[ε]). -/
def productChart : A⊗[k]Dual k ≃ₐ[A] Dual A :=
  AlgEquiv.ofBijective intoDual ⟨left_inverse.injective,right_inverse.surjective⟩

/-- Under the genuine affine fibre-product identification, the chart
of the graph is exactly the tensor map j⊗id, not just a closed subset
with the same geometric points. -/
theorem graph_on_tensor (j : A →ₐ[k] Jet k) (a : A) (z : Dual k) :
    graph j (productChart (a⊗ₜ[k]z)) = j a * z := by
  change graph j (intoDual (a⊗ₜ[k]z)) = _
  rw [tensor_read]
  apply TrivSqZeroExt.ext
  · change (j (a * algebraMap k A z.fst)).fst = (j a * z).fst
    rw [map_mul, j.commutes, TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_mul]
    rfl
  · change (j (a * algebraMap k A z.fst)).snd +
      (j (a * algebraMap k A z.snd)).fst = (j a * z).snd
    rw [map_mul, map_mul, j.commutes, j.commutes, mul_snd,
      TrivSqZeroExt.fst_mul, mul_snd]
    change (j a).fst * 0 + z.fst * (j a).snd + (j a).fst * z.snd =
      (j a).fst * z.snd + z.fst * (j a).snd
    rw [mul_zero, zero_add, add_comm]

end OriginalSameJActualGraphBaseChange318

#print axioms OriginalSameJActualGraphBaseChange318.tensor_read
#print axioms OriginalSameJActualGraphBaseChange318.dual_read
#print axioms OriginalSameJActualGraphBaseChange318.productChart
#print axioms OriginalSameJActualGraphBaseChange318.graph_on_tensor
