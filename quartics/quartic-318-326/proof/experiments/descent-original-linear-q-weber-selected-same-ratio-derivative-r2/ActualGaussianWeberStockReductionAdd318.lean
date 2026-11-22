module
public import ActualGaussianWeberOrdinaryStock318
public import ActualGaussianWeberMixedStock318
public section
noncomputable section

namespace ActualGaussianWeberStockReductionAdd318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberMixedStock318
open ActualGaussianWeberOrdinaryStock318

variable {F : Type*} [Field F] [DecidableEq F] (V : ValuationSubring F)
variable [DecidableEq (ResidueField V)]

private theorem mixed_of_reduction (h2 : (2:ResidueField V) ≠ 0) (P Q : WP F)
    (hP : specialize V h2 P=Point.zero) (hQ : specialize V h2 Q≠Point.zero) :
    specialize V h2 (P+Q)=specialize V h2 Q := by
  cases Q with
  | zero => exact False.elim (hQ rfl)
  | some x y h =>
    have hx : x∈V := by
      by_contra H
      exact hQ ((specialize_some_eq_zero V h2 h).mpr H)
    let a : V := ⟨x,hx⟩
    let b : V := ⟨y,integral_y V ((literal_equation x y).mp h.1) hx⟩
    exact mixed_kernel_finite V h2 P a b h hP

private theorem ordinary_of_reduction (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    (P Q : WP F) (hP : specialize V h2 P≠Point.zero) (hQ : specialize V h2 Q≠Point.zero) :
    specialize V h2 (P+Q)=specialize V h2 P+specialize V h2 Q := by
  cases P with
  | zero => exact False.elim (hP rfl)
  | some x y hP₁ =>
    cases Q with
    | zero => exact False.elim (hQ rfl)
    | some z w hQ₁ =>
      have hx : x∈V := by
        by_contra H
        exact hP ((specialize_some_eq_zero V h2 hP₁).mpr H)
      have hz : z∈V := by
        by_contra H
        exact hQ ((specialize_some_eq_zero V h2 hQ₁).mpr H)
      let a : V := ⟨x,hx⟩
      let b : V := ⟨y,integral_y V ((literal_equation x y).mp hP₁.1) hx⟩
      let c : V := ⟨z,hz⟩
      let d : V := ⟨w,integral_y V ((literal_equation z w).mp hQ₁.1) hz⟩
      exact ordinary_add V hF h2 a b c d hP₁ hQ₁

/-- The two genuine finite branches already force closure of the
kernel: translate by the literal affine point T₀=(0,0) and cancel
its finite residue. No normalized chord through two kernel points
is used, and the existence of T₀ needs no Henselian assumption. -/
private theorem both_kernel (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    (P Q : WP F) (hP : specialize V h2 P=Point.zero)
    (hQ : specialize V h2 Q=Point.zero) : specialize V h2 (P+Q)=Point.zero := by
  have hE : (0:F)^2=0^3-0 := by norm_num
  let T : WP F := Point.some 0 0 (nonsing_of_equation hF hE)
  have hT : specialize V h2 T≠Point.zero := by
    intro hz
    exact ((specialize_some_eq_zero V h2 (nonsing_of_equation hF hE)).mp hz) V.zero_mem
  have hQT := mixed_of_reduction V h2 Q T hQ hT
  have hRight : specialize V h2 (Q+T)≠Point.zero := fun h => hT (hQT.symm.trans h)
  have hPQT := mixed_of_reduction V h2 P (Q+T) hP hRight
  have hSum : specialize V h2 ((P+Q)+T)=specialize V h2 T := by
    rw [add_assoc]
    exact hPQT.trans hQT
  by_contra hn
  have hOpen := ordinary_of_reduction V hF h2 (P+Q) T hn hT
  have hCancel : specialize V h2 (P+Q)+specialize V h2 T =
      (0 : WP (ResidueField V))+specialize V h2 T :=
    hOpen.symm.trans (hSum.trans (zero_add _).symm)
  exact hn (add_right_cancel hCancel)

/-- The already verified ordinary and mixed stock formulas, together
with translation by the literal (0,0), give whole addition for the
same specialization, including all pairs reducing to infinity. -/
theorem specialize_add (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0) (P Q : WP F) :
    specialize V h2 (P+Q)=specialize V h2 P+specialize V h2 Q := by
  by_cases hP : specialize V h2 P=Point.zero
  · by_cases hQ : specialize V h2 Q=Point.zero
    · have hP₀ : specialize V h2 P=0 := hP
      have hQ₀ : specialize V h2 Q=0 := hQ
      rw [hP₀,hQ₀,add_zero]
      exact both_kernel V hF h2 P Q hP hQ
    · have hP₀ : specialize V h2 P=0 := hP
      rw [hP₀,zero_add]
      exact mixed_of_reduction V h2 P Q hP hQ
  · by_cases hQ : specialize V h2 Q=Point.zero
    · have hQ₀ : specialize V h2 Q=0 := hQ
      rw [hQ₀,add_zero,add_comm P Q]
      exact mixed_of_reduction V h2 Q P hQ hP
    · exact ordinary_of_reduction V hF h2 P Q hP hQ

/-- The actual same-place point reduction is an additive homomorphism.
No origin-chord donor is imported. -/
@[expose] def specializeHom (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0) :
    WP F →+ WP (ResidueField V) where
  toFun := specialize V h2
  map_zero' := rfl
  map_add' := specialize_add V hF h2

theorem specializeHom_surjective [HenselianLocalRing V]
    (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0) :
    Function.Surjective (specializeHom V hF h2) := specialize_surjective V hF h2

theorem specialize_fibre_sub (hF : (2:F) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    (P Q : WP F) (h : specialize V h2 P=specialize V h2 Q) :
    specialize V h2 (P-Q)=Point.zero := by
  have he : specializeHom V hF h2 P = specializeHom V hF h2 Q := h
  change specializeHom V hF h2 (P-Q)=0
  rw [map_sub,he,sub_self]

end ActualGaussianWeberStockReductionAdd318
