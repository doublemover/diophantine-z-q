module
public import PELOriginalCM210OriginalRadicalEmbedding318
public section
noncomputable section
namespace PELOriginalCM210RadicalGeneration318
open PELOriginalCM210RadicalTower318 PELOriginalCM210RadicalGenerators318
lemma quadratic_coordinates {F : Type*} [CommRing F] (a : F)
    (z : QuadraticAlgebra F a 0) : z=algebraMap F (QuadraticAlgebra F a 0) z.re+
      algebraMap F (QuadraticAlgebra F a 0) z.im*QuadraticAlgebra.omega := by
  ext <;> simp [QuadraticAlgebra.omega]
lemma first_image_mem (S : Subalgebra ℚ H) (h : ∀i,generator i∈S) (z : First) :
    algebraMap First H z∈S := by
  rw [quadratic_coordinates (-2) z,map_add,map_mul]
  simp only [←IsScalarTower.algebraMap_apply ℚ First H]
  exact add_mem (S.algebraMap_mem z.re) (mul_mem (S.algebraMap_mem z.im) (h 0))
lemma second_image_mem (S : Subalgebra ℚ H) (h : ∀i,generator i∈S) (z : Second) :
    algebraMap Second H z∈S := by
  rw [quadratic_coordinates _ z,map_add,map_mul]
  simp only [←IsScalarTower.algebraMap_apply First Second H]
  exact add_mem (first_image_mem S h z.re) (mul_mem (first_image_mem S h z.im) (h 1))
lemma third_image_mem (S : Subalgebra ℚ H) (h : ∀i,generator i∈S) (z : Third) :
    algebraMap Third H z∈S := by
  rw [quadratic_coordinates _ z,map_add,map_mul]
  simp only [←IsScalarTower.algebraMap_apply Second Third H]
  exact add_mem (second_image_mem S h z.re) (mul_mem (second_image_mem S h z.im) (h 2))
lemma all_mem (S : Subalgebra ℚ H) (h : ∀i,generator i∈S) (z : H) : z∈S := by
  rw [quadratic_coordinates _ z]
  exact add_mem (third_image_mem S h z.re) (mul_mem (third_image_mem S h z.im) (h 3))
lemma adjoin_generators : Algebra.adjoin ℚ (Set.range generator)=⊤ := by
  apply top_unique
  intro z hz
  exact all_mem _ (fun i => Algebra.subset_adjoin ⟨i,rfl⟩) z

end PELOriginalCM210RadicalGeneration318
