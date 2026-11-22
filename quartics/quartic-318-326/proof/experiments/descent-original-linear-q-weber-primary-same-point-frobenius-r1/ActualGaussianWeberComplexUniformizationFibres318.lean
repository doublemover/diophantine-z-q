module
public import ActualGaussianComplexTorusKernel318
public import ActualGaussianWeberGaussianScalarCore318
public import ActualGaussianWeberOriginalUniformization318
public import ActualGaussianWeberSelectedGaussianPrime318
public section
noncomputable section

namespace ActualGaussianWeberComplexUniformizationFibres318

open ActualGaussianComplexTorusKernel318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberQuarterTurn318
open ActualGaussianWeberGaussianScalarSpecialization318 ActualGaussianWeberSelectedGaussianPrime318

attribute [local instance] Classical.decEq

private theorem iota_i : iota gaussianI=Complex.I := by
  change (((⟨0,1⟩ : GaussianInt):ℂ))=Complex.I
  rw [GaussianInt.toComplex_def'] <;> simp

private theorem scalar_int (a : ℤ) (Q : Torus) :
    scalar (a:GaussianInt) Q=a • Q := by
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk'_surjective lattice Q
  rw [scalar_on,map_intCast,←zsmul_eq_mul,map_zsmul]

private theorem scalar_pair (a b : ℤ) (Q : Torus) :
    scalar (literal a b) Q = a • Q+b • scalar gaussianI Q := by
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk'_surjective lattice Q
  rw [scalar_on,scalar_on,iota_i,←map_zsmul,←map_zsmul,←map_add]
  have he : iota (literal a b)=(a:ℂ)+(b:ℂ)*Complex.I := by
    change (((⟨a,b⟩:GaussianInt):ℂ))=_
    exact GaussianInt.toComplex_def' a b
  apply congrArg V
  rw [he,zsmul_eq_mul,zsmul_eq_mul] <;> ring

private theorem scalar_intertwines (U : OriginalUniformization) (a b : ℤ) (P : Torus) :
    U.point (scalar (literal a b) P) =
      gaussian (by norm_num : (2:ℂ)≠0) Complex.I Complex.I_sq a b (U.point P) := by
  rw [scalar_pair,map_add,map_zsmul,map_zsmul,U.quarter] <;> rfl

private def transport_fibre (U : OriginalUniformization) (g : GaussianInt) (h : g≠0)
    (F : WP ℂ →+ WP ℂ)
    (hF : ∀ Q : Torus, U.point (scalar g Q)=F (U.point Q)) (Q : WP ℂ) :
    (GaussianInt ⧸ Ide g) ≃ {P : WP ℂ // F P=Q} := by
  refine (fibre_equiv g h (U.point.symm Q)).trans ?_
  exact
    { toFun := fun P => ⟨U.point P.val,by rw [←hF,P.property,U.point.apply_symm_apply]⟩
      invFun := fun P => ⟨U.point.symm P.val,by
        apply U.point.injective
        simp only [hF,U.point.apply_symm_apply,P.property]⟩
      left_inv := fun P => Subtype.ext (U.point.symm_apply_apply P.val)
      right_inv := fun P => Subtype.ext (U.point.apply_symm_apply P.val) }

/-- The literal prime Gaussian map on the stock curve has exactly p
points in every fibre, furnished by the already realized quotient
at the actual signed prime. -/
theorem actual_complex_prime_fibres (U : OriginalUniformization) (p : ℕ)
    (hp : p.Prime) (a b : ℤ) (hn : a^2+b^2=(p:ℤ)) :
    let G := gaussian (by norm_num : (2:ℂ)≠0) Complex.I Complex.I_sq a b
    ∀ Q : WP ℂ, Finite {P : WP ℂ // G P=Q} ∧ Nat.card {P : WP ℂ // G P=Q}=p := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let g := literal a b
  have hN : g.norm=(p:ℤ) := (norm_literal a b).trans hn
  have h0 : g≠0 := by
    intro he
    rw [he,Zsqrtd.norm_zero] at hN
    exact hp.ne_zero (by exact_mod_cast hN.symm)
  have hQ : Ide g = selectedIdeal (rootOf (p:=p) a b) (rootOf_sq a b hn) :=
    (original_pair_selected_ideal a b hn).symm
  let e : (GaussianInt ⧸ Ide g) ≃ ZMod p :=
    (Ideal.quotEquivOfEq hQ).toEquiv.trans (quotientEquiv _ _).toEquiv
  dsimp only
  intro Q
  let D := transport_fibre U g h0 _ (scalar_intertwines U a b) Q
  let eqv := D.symm.trans e
  exact ⟨Finite.of_injective eqv eqv.injective,
    (Nat.card_congr eqv).trans (by rw [Nat.card_eq_fintype_card,ZMod.card])⟩

/-- The exact same-map complex fibre statement consumed by the
selected prime-field normalization. -/
@[expose] def LiteralComplexFibres : Prop :=
  ∀ (p : ℕ), p.Prime → ∀ a b : ℤ, a^2+b^2=(p:ℤ) →
    let G := gaussian (by norm_num : (2:ℂ)≠0) Complex.I Complex.I_sq a b
    ∀ Q : WP ℂ, Finite {P : WP ℂ // G P=Q} ∧ Nat.card {P : WP ℂ // G P=Q}=p

/-- A single genuine positive-i uniformization supplies every literal
prime count. This statement has neither a rational-function degree
assumption nor any selected local residue information. -/
theorem literal_complex_fibres (U : OriginalUniformization) : LiteralComplexFibres :=
  fun p hp a b hn => actual_complex_prime_fibres U p hp a b hn

end ActualGaussianWeberComplexUniformizationFibres318
