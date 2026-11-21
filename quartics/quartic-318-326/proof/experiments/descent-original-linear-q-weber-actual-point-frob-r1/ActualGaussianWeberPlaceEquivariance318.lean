module
public import ActualGaussianWeberHenselianPointMap318
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.CharP.Frobenius
public section
noncomputable section

namespace ActualGaussianWeberPlaceEquivariance318

open IsLocalRing WeierstrassCurve WeierstrassCurve.Affine
open ActualGaussianWeberHenselianPointMap318

variable {K L : Type*} [Field K] [Field L]

theorem mapped_nonsingular (f : K →+* L) (hL : (2:L) ≠ 0)
    {x y : K} (h : (curve K).toAffine.Nonsingular x y) :
    (curve L).toAffine.Nonsingular (f x) (f y) := by
  apply nonsing_of_equation hL
  simpa only [map_pow,map_sub] using congrArg f ((literal_equation x y).mp h.1)

/-- Literal coordinate action on the stock rational points of the
fixed Weber model, including infinity. -/
@[expose] def onCurvePoint (f : K →+* L) (hL : (2:L) ≠ 0) : WP K → WP L
  | Point.zero => Point.zero
  | Point.some x y h => Point.some (f x) (f y) (mapped_nonsingular f hL h)

variable (V : ValuationSubring K)

/-- The same valuation subring, not just an isomorphic residue place. -/
theorem same_place_iff (σ : K ≃+* K) :
    V.comap σ.toRingHom=V ↔ ∀ x : K, σ x∈V ↔ x∈V := by
  constructor
  · intro h x
    exact (ValuationSubring.mem_comap (A:=V) (f:=σ.toRingHom) (x:=x)).symm.trans
      (by rw [h])
  · intro h
    apply ValuationSubring.ext _ _
    intro x
    exact (ValuationSubring.mem_comap (A:=V) (f:=σ.toRingHom) (x:=x)).trans (h x)

/-- Restrict the selected field automorphism to its actual stable
valuation subring, including its unique inverse restriction. -/
@[expose] def restrict (σ : K ≃+* K) (hσ : V.comap σ.toRingHom=V) : V ≃+* V where
  toFun z := ⟨σ (V.subtype z),((same_place_iff V σ).mp hσ _).mpr z.property⟩
  invFun z := ⟨σ.symm (V.subtype z),((same_place_iff V σ).mp hσ _).mp
    (by simpa only [σ.apply_symm_apply] using z.property)⟩
  left_inv z := Subtype.ext (σ.symm_apply_apply (V.subtype z))
  right_inv z := Subtype.ext (σ.apply_symm_apply (V.subtype z))
  map_mul' a b := Subtype.ext (map_mul σ (V.subtype a) (V.subtype b))
  map_add' a b := Subtype.ext (map_add σ (V.subtype a) (V.subtype b))

@[expose] def residueSigma (σ : K ≃+* K) (hσ : V.comap σ.toRingHom=V) :
    ResidueField V ≃+* ResidueField V := ResidueField.mapEquiv (restrict V σ hσ)

theorem residueSigma_residue (σ : K ≃+* K) (hσ : V.comap σ.toRingHom=V) (a : V) :
    residueSigma V σ hσ (residue V a)=residue V (restrict V σ hσ a) := by
  unfold residueSigma
  rw [ResidueField.mapEquiv_apply,ResidueField.map_residue] <;> rfl

private theorem some_transport {x y x' y' : ResidueField V}
    {h : (curve (ResidueField V)).toAffine.Nonsingular x y}
    {h' : (curve (ResidueField V)).toAffine.Nonsingular x' y'}
    (hx : x=x') (hy : y=y') :
    Point.some x y h=Point.some x' y' h' := by
  subst x'
  subst y'
  rfl

/-- Exact coordinate covariance of the actual same-place reduction
for a field automorphism. No postulated residue action is used. -/
theorem specialize_sigma (hK : (2:K) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    (σ : K ≃+* K) (hσ : V.comap σ.toRingHom=V) (P : WP K) :
    specialize V h2 (onCurvePoint σ.toRingHom hK P) =
      onCurvePoint (residueSigma V σ hσ).toRingHom h2 (specialize V h2 P) := by
  classical
  cases P with
  | zero => rfl
  | some x y h =>
    by_cases hx : x∈V
    · have hσx : σ x∈V := ((same_place_iff V σ).mp hσ x).mpr hx
      let a : V := ⟨x,hx⟩
      let b : V := ⟨y,integral_y V ((literal_equation x y).mp h.1) hx⟩
      have ha : (⟨σ x,hσx⟩ : V)=restrict V σ hσ a := Subtype.ext rfl
      have hb (hy : σ y∈V) : (⟨σ y,hy⟩ : V)=restrict V σ hσ b := Subtype.ext rfl
      simp only [onCurvePoint,specialize,dif_pos hx,dif_pos hσx,finiteReduction]
      exact some_transport V
        (by change residue V (⟨σ x,hσx⟩ : V)=residueSigma V σ hσ (residue V a)
            rw [ha,residueSigma_residue])
        (by change residue V (⟨σ y,_⟩ : V)=residueSigma V σ hσ (residue V b)
            rw [hb,residueSigma_residue])
    · have hσx : σ x∉V := fun h => hx (((same_place_iff V σ).mp hσ x).mp h)
      simp only [onCurvePoint,specialize,dif_neg hx,dif_neg hσx]

section ArithmeticPower

variable {A : Type*} [CommRing A] (aV : A →+* V)
variable (p f : ℕ) [ExpChar (ResidueField V) p]

/-- To identify the residue action with the actual arithmetic Frobenius
x ↦ x^(p^f), it suffices to prove the congruence on residue representatives
from the chosen integral source. -/
theorem residueSigma_eq_power (σ : K ≃+* K) (hσ : V.comap σ.toRingHom=V)
    (hA : Function.Surjective ((residue V).comp aV))
    (hσA : ∀ a : A, residue V (restrict V σ hσ (aV a))=(residue V (aV a))^(p^f)) :
    (residueSigma V σ hσ).toRingHom=iterateFrobenius (ResidueField V) p f := by
  apply RingHom.ext
  intro z
  obtain ⟨a,ha⟩ := hA z
  change residue V (aV a)=z at ha
  rw [←ha]
  change residueSigma V σ hσ (residue V (aV a))=
    iterateFrobenius (ResidueField V) p f (residue V (aV a))
  rw [residueSigma_residue,iterateFrobenius_def]
  exact hσA a

theorem specialize_arithmetic_power (hK : (2:K) ≠ 0) (h2 : (2:ResidueField V) ≠ 0)
    (σ : K ≃+* K) (hσ : V.comap σ.toRingHom=V)
    (hA : Function.Surjective ((residue V).comp aV))
    (hσA : ∀ a : A, residue V (restrict V σ hσ (aV a))=(residue V (aV a))^(p^f))
    (P : WP K) :
    specialize V h2 (onCurvePoint σ.toRingHom hK P) =
      onCurvePoint (iterateFrobenius (ResidueField V) p f) h2 (specialize V h2 P) := by
  rw [specialize_sigma V hK h2 σ hσ P,residueSigma_eq_power V aV p f σ hσ hA hσA]

end ArithmeticPower

end ActualGaussianWeberPlaceEquivariance318
