module
public import VaryingSourcePointNaturality318
public import VaryingSourceTensorAction318
public import Mathlib.RingTheory.TensorProduct.Maps
public section
noncomputable section
namespace VaryingSourceSurjectiveCoefficient318
open VaryingSourceActionClassifier318 VaryingSourceTensorAction318
open VaryingSourcePointNaturality318 CyclicQuotientEvaluation318
open scoped TensorProduct
universe u
variable (R A ι S T : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T]
variable (f : S →ₐ[R] T) (a : Action R A ι S)
@[expose] def mapAction : Action R A ι T :=
  action R A ι T (mapPoint R A ι S T f (point R A ι S a))
lemma mapAction_map (x : A) :
    (mapAction R A ι S T f a).map x=(fun i j => f (a.map x i j)) := rfl
lemma mapAction_marked :
    (mapAction R A ι S T f a).marked=(fun i => f (a.marked i)) := rfl

lemma evaluation_map (z : S ⊗[R] A) :
    evaluation (linearAction R A ι T (mapAction R A ι S T f a))
      (mapAction R A ι S T f a).marked
      (Algebra.TensorProduct.map f (AlgHom.id R A) z)=
    fun i => f (evaluation (linearAction R A ι S a) a.marked z i) := by
  induction z using TensorProduct.induction_on with
  | zero => ext i; simp only [map_zero,Pi.zero_apply]
  | tmul s x =>
    rw [Algebra.TensorProduct.map_tmul]
    change linearAction R A ι T (mapAction R A ι S T f a)
      (f s ⊗ₜ[R] x) (mapAction R A ι S T f a).marked=
      fun i => f (linearAction R A ι S a (s ⊗ₜ[R] x) a.marked i)
    rw [linearAction_tmul,linearAction_tmul,mapAction_map,mapAction_marked]
    ext i
    simp only [Matrix.smul_mulVec,Pi.smul_apply,smul_eq_mul,
      Matrix.mulVec_apply_eq_sum,map_mul,map_sum]
  | add x y hx hy =>
    rw [map_add,map_add,hx,hy]
    ext i
    simp only [Pi.add_apply,map_add]

/-- In particular cyclicity survives passage to a residue field. The
surjectivity of the coefficient map is explicit here; no arbitrary base
change theorem is claimed by this lemma. -/
lemma cyclic_of_surjective (hf : Function.Surjective f)
    (h : Function.Surjective (evaluation (linearAction R A ι S a) a.marked)) :
    Function.Surjective (evaluation (linearAction R A ι T (mapAction R A ι S T f a))
      (mapAction R A ι S T f a).marked) := by
  intro y
  choose ys hys using fun i => hf (y i)
  obtain ⟨z,hz⟩ := h ys
  refine ⟨Algebra.TensorProduct.map f (AlgHom.id R A) z,?_⟩
  rw [evaluation_map,hz]
  exact funext hys
lemma determinant_map (w : ι → List A) :
    f (VaryingMatrixWords318.determinant (point R A ι S a).val w)=
      VaryingMatrixWords318.determinant (point R A ι T (mapAction R A ι S T f a)).val w := by
  have hp : point R A ι T (mapAction R A ι S T f a)=
      mapPoint R A ι S T f (point R A ι S a) :=
    (actionPoints R A ι T).symm_apply_apply (mapPoint R A ι S T f (point R A ι S a))
  rw [hp]
  exact VaryingMatrixWords318.determinant_map R f (point R A ι S a).val w
end VaryingSourceSurjectiveCoefficient318
