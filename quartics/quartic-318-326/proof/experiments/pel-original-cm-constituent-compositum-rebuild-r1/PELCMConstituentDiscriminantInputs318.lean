module
public import PELCMConstituentScalarTowers318
public import Mathlib.RingTheory.Coprime.Basic
public section
noncomputable section
namespace PELCMConstituentDiscriminantInputs318
open PELCMQuadraticConstituentFields318 PELCMQuadraticConstituentOrders318
open PELCMConstituentFieldEmbeddings318
@[expose] def bezout : Fin 4 → Fin 4 → ℤ :=
  ![![0, 1, -2, -1], ![-3, 0, -2, 2], ![-3, -1, 0, 3], ![1, -1, 2, 0]]
lemma coprime_discriminants (i j : Fin 4) (h : i ≠ j) :
    IsCoprime (NumberField.discr (Field i)) (NumberField.discr (Field j)) := by
  rw [native_discriminant, native_discriminant]
  refine ⟨bezout i j, bezout j i, ?_⟩
  fin_cases i <;> fin_cases j <;> norm_num [discriminant, bezout] at h ⊢
lemma discriminant_product :
    NumberField.discr (Field 0) * NumberField.discr (Field 1) *
      NumberField.discr (Field 2) * NumberField.discr (Field 3) = -840 := by
  simp only [native_discriminant]
  norm_num [discriminant]
/-- The full native constituent orders and their embeddings now concern the
same H. This is an input packet, not a claim about the full integer ring of H. -/
lemma actual_compositum_inputs :
    compositum = ⊤ ∧
    (∀ i j : Fin 4, i ≠ j →
      IsCoprime (NumberField.discr (Field i)) (NumberField.discr (Field j))) ∧
    (∀ i : Fin 4, Module.finrank ℚ (Field i) = 2) :=
  ⟨compositum_eq_top, coprime_discriminants,
    PELCMConstituentScalarTowers318.constituent_degree⟩
end PELCMConstituentDiscriminantInputs318
