module
public import OriginalPrincipalLocalization318
public import Mathlib.Data.Finset.Lattice.Fold
public section
noncomputable section
namespace OriginalPrincipalUniformClearing318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite OriginalPrincipalLocalization318
universe u v
variable (X : Scheme.{u}) {ι : Type v} [Fintype ι]
  (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (s : Γ(X,⊤))

include hU in
/-- One actual denominator exponent works on the entire finite family of
original affine opens, including empty opens and nilpotent coefficients. -/
theorem clear_family (z : ∀ i, Γ(X,X.basicOpen s ⊓ U i)) :
    ∃ n : ℕ, ∃ a : ∀ i, Γ(X,U i), ∀ i,
      (coefficient X (X.basicOpen s ⊓ U i) s)^n * z i = res X inf_le_right (a i) := by
  classical
  choose n a ha using fun i => OriginalPrincipalLocalization318.clear X (U i) (hU i) s (z i)
  let N := Finset.univ.sup n
  have hn (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N,fun i => (coefficient X (U i) s)^(N-n i) * a i,fun i => ?_⟩
  rw [map_mul,map_pow,res_coefficient,← ha]
  rw [← mul_assoc,← pow_add,Nat.sub_add_cancel (hn i)]

include hU in
/-- A uniform power kills every member of a finite family of original
localization kernels. No kernel element is asserted to be zero before
this explicit annihilator is applied. -/
theorem kill_family (a : ∀ i, Γ(X,U i))
    (ha : ∀ i, res X (inf_le_right : X.basicOpen s ⊓ U i ≤ U i) (a i) = 0) :
    ∃ n : ℕ, ∀ i, (coefficient X (U i) s)^n * a i = 0 := by
  classical
  choose n hn using fun i => OriginalPrincipalLocalization318.kill X (U i) (hU i) s (a i) (ha i)
  let N := Finset.univ.sup n
  have hN (i : ι) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  refine ⟨N,fun i => ?_⟩
  calc
    _ = (coefficient X (U i) s)^(N-n i) * ((coefficient X (U i) s)^(n i) * a i) := by
      rw [← mul_assoc,← pow_add,Nat.sub_add_cancel (hN i)]
    _ = 0 := by rw [hn,mul_zero]
end OriginalPrincipalUniformClearing318
