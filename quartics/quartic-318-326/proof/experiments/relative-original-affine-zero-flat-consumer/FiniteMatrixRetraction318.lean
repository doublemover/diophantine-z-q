module
public import ScalarRetractionIdeal318
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public section
noncomputable section
namespace FiniteMatrixRetraction318
universe u
variable {R A B : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

/-- The adjugate turns an actual finite approximate retraction into a
scalar retraction. The finite coordinates need not be a basis of all A. -/
lemma determinant_mem_scalars (f : A →ₗ[R] B) (s : Finset A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : (ι → R) →ₗ[R] A) (g : B →ₗ[R] (ι → R)) (T : Matrix ι ι R)
    (hs : ∀ a ∈ s, ∃ v, e v = a)
    (hT : ∀ v, g (f (e v)) = T *ᵥ v) :
    T.det ∈ ScalarRetractionIdeal318.scalars f s := by
  refine ⟨e.comp ((Matrix.mulVecLin T.adjugate).comp g), ?_⟩
  intro a ha
  obtain ⟨v, rfl⟩ := hs a ha
  change e (T.adjugate *ᵥ g (f (e v))) = T.det • e v
  rw [hT, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, map_smul]

/-- A finite matrix reducing to the identity has determinant outside the
specified maximal ideal. This statement retains the literal integral
matrix; no change of integer lattice or discarded parity is involved. -/
lemma determinant_not_mem (m : Ideal R) [m.IsMaximal]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι R)
    (hT : T.map (Ideal.Quotient.mk m) = 1) : T.det ∉ m := by
  intro hmem
  have hz : Ideal.Quotient.mk m T.det = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have ho : Ideal.Quotient.mk m T.det = 1 := by
    rw [RingHom.map_det]
    change (T.map (Ideal.Quotient.mk m)).det = 1
    rw [hT, Matrix.det_one]
  exact one_ne_zero (ho.symm.trans hz)

/-- Residue-identity matrix certificates on every finite set produce
universal tensor injectivity. Constructing these certificates from the
actual field-fiber map remains an explicit geometric/algebraic task. -/
lemma tensor_injective (f : A →ₗ[R] B)
    (h : ∀ s : Finset A, ∀ m : Ideal R, m.IsMaximal →
      ∃ (n : ℕ) (e : (Fin n → R) →ₗ[R] A) (g : B →ₗ[R] (Fin n → R))
        (T : Matrix (Fin n) (Fin n) R),
        (∀ a ∈ s, ∃ v, e v = a) ∧
        (∀ v, g (f (e v)) = T *ᵥ v) ∧ T.map (Ideal.Quotient.mk m) = 1)
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (f.lTensor N) := by
  apply ScalarRetractionIdeal318.tensor_injective f _ N
  intro s m hm
  letI : m.IsMaximal := hm
  obtain ⟨n, e, g, T, hs, he, hT⟩ := h s m hm
  exact ⟨T.det, determinant_mem_scalars f s e g T hs he,
    determinant_not_mem m T hT⟩
end FiniteMatrixRetraction318
