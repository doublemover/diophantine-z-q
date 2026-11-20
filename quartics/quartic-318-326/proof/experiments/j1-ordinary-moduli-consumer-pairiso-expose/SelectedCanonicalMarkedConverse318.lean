module
public import SelectedPrimitiveTwistPoint318
public import SelectedRelativeAffineSignDescent318
public import SelectedMarkedNormalization318
public section
noncomputable section
open SelectedPrimitiveAffineSign318 SelectedPrimitiveFixedX318 SelectedPrimitiveTwistPoint318
open SelectedMarkedNormalization318

namespace SelectedCanonicalMarkedConverse318
variable (n : ℕ) (I : Ideal (D n))
local notation "R" => SelectedPrimitiveAffineSign318.R n
local notation "Q" => D n ⧸ I
variable (τ : Q →ₐ[R] Q) (hτ : τ.comp (q n I) = (q n I).comp (sign n))
local notation "F" => fixed n I τ
local notation "Fₑ" => SelectedPrimitiveRootSignDescent318.Fixed n I τ
local notation "x₀" => fixedX n I τ hτ
local notation "xₑ" => SelectedFixedGeneratorGlue318.generator n I τ hτ

/-- Both fixed-ring presentations use the actual sign equation on Q. -/
@[expose] def intoEqualizer : F →ₐ[R] Fₑ where
  toFun z := ⟨(z:Q),by
    change τ (z:Q) = (z:Q)
    exact z.property⟩
  map_one' := Subtype.ext rfl
  map_mul' _ _ := Subtype.ext rfl
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  commutes' _ := Subtype.ext rfl

@[simp] theorem intoEqualizer_x : intoEqualizer n I τ x₀ = xₑ := Subtype.ext rfl

/-- Normalized abscissa prescribes the entire algebra map on the actual
fixed quotient, including over rings with nilpotents. -/
include hτ in
theorem alg_ext {S : Type*} [CommRing S] [Algebra R S] {f g : F →ₐ[R] S}
    (hx : f x₀ = g x₀) : f = g := by
  apply AlgHom.ext
  intro z
  have hz : τ (z:Q) = (z:Q) := z.property
  obtain ⟨p,hp⟩ := (fixed_iff_polynomial n I τ hτ (z:Q)).mp hz
  have hz' : Polynomial.aeval x₀ p = z := by
    apply Subtype.val_injective
    have hh : F.val.comp (Polynomial.aeval x₀) = Polynomial.aeval (xbar n I) := by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply,Polynomial.aeval_X] <;> rfl
    change (F.val.comp (Polynomial.aeval x₀)) p = (z:Q)
    rwa [hh]
  have hfg : f.comp (Polynomial.aeval x₀) = g.comp (Polynomial.aeval x₀) := by
    apply Polynomial.algHom_ext
    simpa only [AlgHom.comp_apply,Polynomial.aeval_X] using hx
  rw [←hz']
  exact DFunLike.congr_fun hfg p

variable (S : Type) [CommRing S] [Algebra R S] (c : Sˣ)
local notation "U" => EvenContactEtale318.RootRing c
local notation "u" => SelectedRelativeAffineSignDescent318.rootUnit S c

/-- Effective inverse on the actual canonical chart from the evaluation of
the same inverse-normalized primitive mark on its square-root cover. -/
theorem class_exists [Nontrivial S] (x : S) (mark : Q →ₐ[R] U)
    (hx : mark (xbar n I) = (↑u⁻¹:U)^2 * algebraMap S U x) :
    ∃! f : F →ₐ[R] S, f x₀ = abscissa c x := by
  obtain ⟨g,hg,_⟩ := SelectedRelativeAffineSignDescent318.relative_descends n I τ hτ S c mark x hx
  let f := g.comp (intoEqualizer n I τ)
  have hf : f x₀ = abscissa c x := by
    change g (intoEqualizer n I τ x₀) = _
    rw [intoEqualizer_x n I τ hτ]
    exact hg.2
  exact ⟨f,hf,fun g' hg' => alg_ext n I τ hτ (hg'.trans hf.symm)⟩

/-- An actual pullback of the normalized twist parameter remains the
normalized marked equation's ordinate square, not a chosen scalar. -/
theorem fixed_square_equation (hY : IsUnit (ybar n I)) :
    (twistUnit n I τ hτ hY : Fˣ).val = x₀^3 + algebraMap R F (A n)*x₀ + algebraMap R F (B n) := by
  apply Subtype.val_injective
  simp only [map_add,map_pow,map_mul,AlgHom.commutes,twistUnit_value]
  change (ybar n I)^2 = (xbar n I)^3 +
    algebraMap R Q (A n)*xbar n I + algebraMap R Q (B n)
  have h := congrArg (q n I) (ShortAffineJacobian318.relation (A n) (B n))
  simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes] at h
  linear_combination h

variable (hY : IsUnit (ybar n I)) (f : F →ₐ[R] S) (C D' : S)
variable (P : ShortAffineJacobian318.Ring C D' →ₐ[S] S)
local notation "x" => P (ShortAffineJacobian318.x C D')
local notation "y" => P (ShortAffineJacobian318.y C D')
variable (Y : Sˣ) (hYP : (Y:S) = y)
variable (hC : C = (c:S)^2 * algebraMap R S (A n))
variable (hD : D' = (c:S)^3 * algebraMap R S (B n))
variable (hx : f x₀ = abscissa c x)
local notation "d" => Units.map f.toMonoidHom (twistUnit n I τ hτ hY)
local notation "ρ" => recoveryScale c d Y

include hYP hC hD hx in
theorem actual_square :
    d = ordinateSquare c Y := by
  have he := congrArg f (fixed_square_equation n I τ hτ hY)
  simp only [map_add,map_pow,map_mul,AlgHom.commutes,hx] at he
  have hp := congrArg P (ShortAffineJacobian318.relation C D')
  simp only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes,
    Algebra.algebraMap_self,RingHom.id_apply] at hp
  have hp' : y^2 = x^3+C*x+D' := by linear_combination hp
  rw [hC,hD] at hp'
  have hn := normalized_equation (algebraMap R S (A n)) (algebraMap R S (B n)) x y c hp'
  apply Units.ext
  change f (twistUnit n I τ hτ hY : F) = (↑(ordinateSquare c Y):S)
  simpa only [ordinateSquare,Units.val_mul,Units.val_pow_eq_pow_val,hYP] using he.trans hn.symm

include hYP hC hD hx in
/-- All four equalities for the actual pointed short scaling from the
given pair to the pullback of the specific canonical twist. -/
theorem transport_eqs :
    f (twistA n I τ hτ hY) = (ρ:S)^4*C ∧
    f (twistB n I τ hτ hY) = (ρ:S)^6*D' ∧
    f (markX n I τ hτ hY) = (ρ:S)^2*x ∧
    f (markY n I τ hτ hY) = (ρ:S)^3*y := by
  have hd := actual_square n I τ hτ S c hY f C D' P Y hYP hC hD hx
  obtain ⟨hρ4,hρ6⟩ := scale_coeff c d Y hd
  have h4 : (ρ:S)^4*(c:S)^2 = (d:S)^2 := by
    simpa only [Units.val_mul,Units.val_pow_eq_pow_val] using
      congrArg (fun v : Sˣ => (v:S)) hρ4
  have h6 : (ρ:S)^6*(c:S)^3 = (d:S)^3 := by
    simpa only [Units.val_mul,Units.val_pow_eq_pow_val] using
      congrArg (fun v : Sˣ => (v:S)) hρ6
  refine ⟨?_,?_,?_,?_⟩
  · simp only [twistA,map_mul,map_pow,AlgHom.commutes,hC]
    change (d:S)^2 * algebraMap R S (A n) = (ρ:S)^4*((c:S)^2*algebraMap R S (A n))
    rw [← mul_assoc,h4]
  · simp only [twistB,map_mul,map_pow,AlgHom.commutes,hD]
    change (d:S)^3 * algebraMap R S (B n) = (ρ:S)^6*((c:S)^3*algebraMap R S (B n))
    rw [← mul_assoc,h6]
  · simp only [markX,map_mul,hx]
    exact (scale_x c d Y x hd).symm
  · simp only [markY,map_pow]
    simpa only [Units.val_mul,Units.val_pow_eq_pow_val,hYP] using
      (congrArg (fun v : Sˣ => (v:S)) (scale_y c d Y hd)).symm

/-- Actual algebra-map agreement after both restrictions into a common
overlap ring. c and x have the same square weight under the transition. -/
theorem overlap {S₁ S₂ T : Type*} [CommRing S₁] [CommRing S₂] [CommRing T]
    [Algebra R S₁] [Algebra R S₂] [Algebra R T]
    (f₁ : F →ₐ[R] S₁) (f₂ : F →ₐ[R] S₂) (l : S₁ →ₐ[R] T) (r : S₂ →ₐ[R] T)
    (c₁ : S₁ˣ) (c₂ : S₂ˣ) (x₁ : S₁) (x₂ : S₂) (v : Tˣ)
    (h₁ : f₁ x₀ = abscissa c₁ x₁) (h₂ : f₂ x₀ = abscissa c₂ x₂)
    (hc : Units.map r.toMonoidHom c₂ = v^2 * Units.map l.toMonoidHom c₁)
    (hX : r x₂ = (v:T)^2 * l x₁) :
    l.comp f₁ = r.comp f₂ := by
  apply alg_ext n I τ hτ
  change l (f₁ x₀) = r (f₂ x₀)
  rw [h₁,h₂,abscissa_map l.toRingHom,abscissa_map r.toRingHom]
  change abscissa (Units.map l.toMonoidHom c₁) (l x₁) =
    abscissa (Units.map r.toMonoidHom c₂) (r x₂)
  rw [hc,hX]
  exact (abscissa_transition _ v _).symm

end SelectedCanonicalMarkedConverse318

#print axioms SelectedCanonicalMarkedConverse318.class_exists
#print axioms SelectedCanonicalMarkedConverse318.transport_eqs
#print axioms SelectedCanonicalMarkedConverse318.overlap
