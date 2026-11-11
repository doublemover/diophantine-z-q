module
public import Mathlib.Algebra.Polynomial.Laurent
public section
noncomputable section
namespace RelativeLaurentModuleShift318
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
  [Module (LaurentPolynomial R) M]

/-- Multiplication by the specified Laurent unit on the SAME module. -/
@[expose] def equivalence (n : ℤ) : M ≃ₗ[LaurentPolynomial R] M where
  toFun x := (LaurentPolynomial.T n : LaurentPolynomial R) • x
  invFun x := (LaurentPolynomial.T (-n) : LaurentPolynomial R) • x
  left_inv x := by
    rw [smul_smul,← LaurentPolynomial.T_add,neg_add_cancel,LaurentPolynomial.T_zero,one_smul]
  right_inv x := by
    rw [smul_smul,← LaurentPolynomial.T_add,add_neg_cancel,LaurentPolynomial.T_zero,one_smul]
  map_add' := smul_add _
  map_smul' := fun _ _ => smul_comm _ _ _

/-- Actual equivalences preserve the span of a specified image. -/
lemma image_span {N M' : Type*} [AddCommGroup M'] [Module (LaurentPolynomial R) M']
    (e : M ≃ₗ[LaurentPolynomial R] M') (f : N → M)
    (hf : Submodule.span (LaurentPolynomial R) (Set.range f) = ⊤) :
    Submodule.span (LaurentPolynomial R) (Set.range (fun x => e (f x))) = ⊤ := by
  apply top_unique
  intro x hx
  obtain ⟨y,rfl⟩ := e.surjective x
  have hy : y ∈ Submodule.span (LaurentPolynomial R) (Set.range f) := by rw [hf]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z,rfl⟩ := hy
    exact Submodule.subset_span ⟨z,rfl⟩
  | zero => simpa only [map_zero] using
      (Submodule.zero_mem (Submodule.span (LaurentPolynomial R) (Set.range (fun x => e (f x)))))
  | add y z _ _ hy hz => simpa only [map_add] using Submodule.add_mem _ hy hz
  | smul a y _ hy => simpa only [map_smul] using Submodule.smul_mem _ a hy

/-- A shift of an actual relation-generating image remains spanning. -/
lemma shifted_span {N : Type*} (f : N → M)
    (hf : Submodule.span (LaurentPolynomial R) (Set.range f) = ⊤) (n : ℤ) :
    Submodule.span (LaurentPolynomial R)
      (Set.range (fun x => equivalence R M n (f x))) = ⊤ :=
  image_span R M (equivalence R M n) f hf
end RelativeLaurentModuleShift318
