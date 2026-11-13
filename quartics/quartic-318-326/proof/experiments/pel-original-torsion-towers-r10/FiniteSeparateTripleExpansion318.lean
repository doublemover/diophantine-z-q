module
public import FiniteSeparateFunctionExpansion318
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public section
noncomputable section
namespace FiniteSeparateTripleExpansion318
variable {K X Y Z I J L : Type*} [Field K] [Fintype I] [Fintype J] [Fintype L]

/-- Three genuine separate finite spans produce ONE constant triple
expansion. Only the actual first two function families need independence. -/
theorem exists_expansion (b : I → X → K) (d : J → Y → K) (e : L → Z → K)
    (hb : LinearIndependent K b) (hd : LinearIndependent K d) (F : X → Y → Z → K)
    (hx : ∀ y z,∃ c : I → K,∀ x,F x y z=∑ i,c i*b i x)
    (hy : ∀ x z,∃ c : J → K,∀ y,F x y z=∑ j,c j*d j y)
    (hz : ∀ x y,∃ c : L → K,∀ z,F x y z=∑ l,c l*e l z) :
    ∃ a : I → J → L → K,∀ x y z,
      F x y z=∑ i,∑ j,∑ l,a i j l*b i x*d j y*e l z := by
  classical
  have hpair (x : X) : ∃ a : J → L → K,∀ y z,
      F x y z=∑ j,∑ l,a j l*d j y*e l z :=
    FiniteSeparateFunctionExpansion318.exists_double_expansion d e hd (F x) (hy x) (hz x)
  let de : J×L → Y×Z → K := fun q yz => d q.1 yz.1*e q.2 yz.2
  have hsecond (x : X) : ∃ c : J×L → K,∀ yz,F x yz.1 yz.2=∑ q,c q*de q yz := by
    obtain ⟨a,ha⟩ := hpair x
    refine ⟨fun q => a q.1 q.2,?_⟩
    rintro ⟨y,z⟩
    simpa only [de,←Finset.univ_product_univ,Finset.sum_product,mul_assoc] using ha y z
  obtain ⟨a,ha⟩ := FiniteSeparateFunctionExpansion318.exists_double_expansion b de hb
    (fun x yz => F x yz.1 yz.2) (fun yz => hx yz.1 yz.2) hsecond
  refine ⟨fun i j l => a i (j,l),?_⟩
  intro x y z
  rw [ha x (y,z)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Finset.univ_product_univ,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  change a i (j,l)*b i x*(d j y*e l z)=_
  ring
end FiniteSeparateTripleExpansion318
