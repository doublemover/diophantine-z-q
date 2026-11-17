module
public import ActualTwoDescentIncidence318
public section
noncomputable section
namespace ActualTwoDescentCore318
open ActualTwoDescentIncidence318
open scoped BigOperators Matrix
set_option maxHeartbeats 16000000

/-- Literal deleted-q0 core [D C; C^t 0], with the original incidence
columns constructed in the preceding module. D need not be artificially
symmetric: the actual proof uses its total sum1. -/
@[expose] def core (d : ℕ) (D : Matrix (Option (Fin d)) (Option (Fin d)) (ZMod 2)) :
    Matrix (Option (Fin d) ⊕ Fin d) (Option (Fin d) ⊕ Fin d) (ZMod 2) :=
  Matrix.fromBlocks D (incidence d) (incidence d).transpose 0

lemma actual_core_equations (d : ℕ)
    (D : Matrix (Option (Fin d)) (Option (Fin d)) (ZMod 2))
    (hD : (∑ i, ∑ j, D i j)=1)
    (x : Option (Fin d) → ZMod 2) (y : Fin d → ZMod 2)
    (hupper : D *ᵥ x + incidence d *ᵥ y=0)
    (hlower : (incidence d).transpose *ᵥ x=0) : x=0 ∧ y=0 := by
  have hx := actual_incidence_transpose_kernel d x hlower
  have hsumD : (∑ i, (D *ᵥ x) i)=x none := by
    simp only [Matrix.mulVec,dotProduct,hx,←Finset.sum_mul,hD,one_mul]
  have hsum := congrArg (fun z : Option (Fin d) → ZMod 2 => ∑ i, z i) hupper
  simp only [Pi.add_apply,Finset.sum_add_distrib,actual_incidence_total,
    add_zero,Pi.zero_apply,Finset.sum_const_zero,hsumD] at hsum
  have hx0 : x=0 := by funext i; exact (hx i).trans hsum
  refine ⟨hx0,?_⟩
  apply actual_incidence_injective d
  simpa only [hx0,Matrix.mulVec_zero,zero_add] using hupper

/-- The whole concrete core has trivial kernel, including d0. -/
theorem actual_core_kernel (d : ℕ)
    (D : Matrix (Option (Fin d)) (Option (Fin d)) (ZMod 2))
    (hD : (∑ i, ∑ j, D i j)=1)
    (z : Option (Fin d) ⊕ Fin d → ZMod 2) (hz : core d D *ᵥ z=0) : z=0 := by
  have he := Matrix.fromBlocks_mulVec D (incidence d) (incidence d).transpose
    (0 : Matrix (Fin d) (Fin d) (ZMod 2)) z
  have hup : D *ᵥ (z ∘ Sum.inl)+incidence d *ᵥ (z ∘ Sum.inr)=0 := by
    funext i
    have h := congrFun (he.symm.trans hz) (Sum.inl i)
    simpa only [Sum.elim_inl,Pi.zero_apply] using h
  have hlo : (incidence d).transpose *ᵥ (z ∘ Sum.inl)=0 := by
    funext i
    have h := congrFun (he.symm.trans hz) (Sum.inr i)
    simpa only [Sum.elim_inr,Matrix.zero_mulVec,Pi.add_apply,Pi.zero_apply,add_zero] using h
  obtain ⟨hx,hy⟩ := actual_core_equations d D hD (z ∘ Sum.inl) (z ∘ Sum.inr) hup hlo
  funext i
  cases i with
  | inl i => exact congrFun hx i
  | inr i => exact congrFun hy i

/-- Nonsingularity is produced, not assumed. This is the exact finite
linear-algebra core needed before enlarging to the second twist support. -/
theorem actual_core_unit (d : ℕ)
    (D : Matrix (Option (Fin d)) (Option (Fin d)) (ZMod 2))
    (hD : (∑ i, ∑ j, D i j)=1) : IsUnit (core d D) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hz : core d D *ᵥ (x-y)=0 := by rw [Matrix.mulVec_sub,hxy,sub_self]
  exact sub_eq_zero.mp (actual_core_kernel d D hD (x-y) hz)

end ActualTwoDescentCore318
