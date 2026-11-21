module
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega
public section

namespace CTFiniteIsogenyOrthogonalCount318

open Module
open LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Algebraic extension of an exact zero-pairing table on generators.
The form need not be alternating (nor is this a finite CT pairing). -/
theorem span_self_orthogonal_of_generators {I : Type*}
    (B : LinearMap.BilinForm K V) (f : I → V)
    (h : ∀ i j, B (f i) (f j)=0) :
    Submodule.span K (Set.range f) ≤ B.orthogonal (Submodule.span K (Set.range f)) := by
  let W := Submodule.span K (Set.range f)
  have hL (j : I) : W ≤ LinearMap.ker (B.flip (f j)) := by
    apply Submodule.span_le.2
    rintro _ ⟨i,rfl⟩
    exact LinearMap.mem_ker.mpr (h i j)
  intro v hv
  apply mem_orthogonal_iff.mpr
  intro u hu
  have hR : W ≤ LinearMap.ker (B u) := by
    apply Submodule.span_le.2
    rintro _ ⟨j,rfl⟩
    exact LinearMap.mem_ker.mpr (LinearMap.mem_ker.mp (hL j hu))
  exact LinearMap.mem_ker.mp (hR hv)

theorem orthogonal_sup (B : LinearMap.BilinForm K V) (W L : Submodule K V) :
    B.orthogonal (W ⊔ L)=B.orthogonal W ⊓ B.orthogonal L := by
  ext v
  constructor
  · intro h
    exact ⟨orthogonal_le le_sup_left h,orthogonal_le le_sup_right h⟩
  · rintro ⟨hW,hL⟩
    apply mem_orthogonal_iff.mpr
    intro u hu
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hu
    rw [add_left,mem_orthogonal_iff.mp hW x hx,mem_orthogonal_iff.mp hL y hy,add_zero]

variable [FiniteDimensional K V]

/-- A half-dimensional isotropic subspace is self-annihilating, even
for a nonalternating form such as the real or dyadic scalar form. -/
theorem self_annihilator_of_half (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W : Submodule K V) (hW : W ≤ B.orthogonal W)
    (hHalf : 2*finrank K W=finrank K V) :
    B.orthogonal W=W := by
  have hd := finrank_orthogonal hB W
  have hl : finrank K (B.orthogonal W) ≤ finrank K W := by omega
  exact (Submodule.eq_of_le_of_finrank_le hW hl).symm

/-- The signed exponent of the finite isogeny-Selmer quotient, once
W is the actual signed support localization and L' is the opposite
local condition. Subtraction is in ℤ, not truncated natural division. -/
theorem finite_ratio_exponent (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate)
    (W L L' : Submodule K V) (hW : B.orthogonal W=W) (hL : B.orthogonal L=L') :
    (finrank K (W ⊓ L : Submodule K V):ℤ)- (finrank K (W ⊓ L' : Submodule K V):ℤ)
      = (finrank K L:ℤ)-(finrank K W:ℤ) := by
  have hJ : B.orthogonal (W⊔L)=W⊓L' := by rw [orthogonal_sup,hW,hL]
  have hD := finrank_orthogonal hB (W⊔L)
  rw [hJ] at hD
  have hRank := Submodule.finrank_sup_add_finrank_inf_eq W L
  have hBound := Submodule.finrank_le (W⊔L)
  omega

end CTFiniteIsogenyOrthogonalCount318

#print axioms CTFiniteIsogenyOrthogonalCount318.span_self_orthogonal_of_generators
#print axioms CTFiniteIsogenyOrthogonalCount318.finite_ratio_exponent
