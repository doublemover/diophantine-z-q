module
public import PELCMShiftedRadicalGenerators318
public section
noncomputable section
namespace PELCMConstituentFieldEmbeddings318
open PELCMQuadraticConstituentFields318 PELCMShiftedRadicalGenerators318
open PELOriginalCM210RadicalTower318
/-- The domain is the same constituent whose full native order was proved. -/
@[expose] def embedding (i : Fin 4) : Field i →ₐ[ℚ] H :=
  QuadraticAlgebra.lift ⟨shifted i, by
    simpa [pow_two, Algebra.smul_def] using shifted_equation i⟩
lemma embedding_omega (i : Fin 4) :
    embedding i (QuadraticAlgebra.omega : Field i) = shifted i := by
  simp [embedding, QuadraticAlgebra.lift, QuadraticAlgebra.omega]
lemma embedding_coordinates (i : Fin 4) (z : Field i) :
    embedding i z = algebraMap ℚ H z.re + algebraMap ℚ H z.im * shifted i := by
  simp [embedding, QuadraticAlgebra.lift, Algebra.smul_def]
lemma embedding_injective (i : Fin 4) : Function.Injective (embedding i) :=
  (embedding i).injective
@[expose] def image (i : Fin 4) : Subalgebra ℚ H := (embedding i).range
lemma shifted_mem_image (i : Fin 4) : shifted i ∈ image i :=
  ⟨QuadraticAlgebra.omega, embedding_omega i⟩
lemma image_le (S : Subalgebra ℚ H) (i : Fin 4) (h : shifted i ∈ S) : image i ≤ S := by
  rintro z ⟨x, rfl⟩
  rw [embedding_coordinates]
  exact S.add_mem (S.algebraMap_mem x.re) (S.mul_mem (S.algebraMap_mem x.im) h)
/-- The compositum is formed from the literal embedded constituent carriers. -/
@[expose] def compositum : Subalgebra ℚ H := ⨆ i, image i
lemma compositum_eq_top : compositum = ⊤ := by
  apply shifted_generate
  intro i
  exact (le_iSup image i) (shifted_mem_image i)
lemma images_generate (S : Subalgebra ℚ H) (h : ∀ i, image i ≤ S) : S = ⊤ :=
  shifted_generate S (fun i => h i (shifted_mem_image i))
end PELCMConstituentFieldEmbeddings318
