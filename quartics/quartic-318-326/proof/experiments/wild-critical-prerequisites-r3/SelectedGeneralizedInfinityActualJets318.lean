module
public import SelectedGeneralizedInfinityCartier318
public section
noncomputable section
open MvPolynomial Algebra
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedInfinityCartier318

namespace SelectedGeneralizedInfinityActualJets318

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
variable [Module Rᵐᵒᵖ V] [IsCentralScalar R V]
local notation "S" => TrivSqZeroExt R V
local notation "fst" => TrivSqZeroExt.fstHom R R V

/-- Actual quotient evaluation on the literal generalized chart,
before inverting its two denominators. -/
@[expose] def raw (d : Rˣ) (v : V) : Chart d →ₐ[R] S := by
  let h := MvPolynomial.aeval ![(TrivSqZeroExt.inr v : S), 0]
  refine Ideal.Quotient.liftₐ _ h ?_
  have hk : Ideal.span (Set.range (equations d)) ≤ RingHom.ker h.toRingHom := by
    apply Ideal.span_le.2
    rintro _ ⟨_,rfl⟩
    change h (equation d) = 0
    have h2 : (TrivSqZeroExt.inr v : S)^2 = 0 := (pow_two _).trans (TrivSqZeroExt.inr_mul_inr R v v)
    have h3 : (TrivSqZeroExt.inr v : S)^3 = 0 := by
      rw [show (3:ℕ) = 2+1 by decide,pow_succ,h2,zero_mul]
    simp [h,equation,h3]
  intro f hf
  exact hk hf

@[simp] theorem raw_parameter (d : Rˣ) (v : V) :
    raw d v (parameter d) = TrivSqZeroExt.inr v := by
  simp [raw,parameter,Ideal.Quotient.liftₐ_apply]

@[simp] theorem raw_ordinate (d : Rˣ) (v : V) :
    raw d v (ordinate d) = 0 := by
  simp [raw,ordinate,Ideal.Quotient.liftₐ_apply]

theorem raw_augmentation (d : Rˣ) (v : V) :
    fst.comp (raw d v) = origin d := by
  apply Ideal.Quotient.algHom_ext R
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · change (raw d v (parameter d)).fst = origin d (parameter d)
    rw [raw_parameter,TrivSqZeroExt.fst_inr,origin_parameter]
  · change (raw d v (ordinate d)).fst = origin d (ordinate d)
    rw [raw_ordinate,TrivSqZeroExt.fst_zero,origin_ordinate]

/-- Each first-order point extends to the actual smooth, identity-isolating
open; the denominator has unit residue 1 in every characteristic. -/
@[expose] def point (d : Rˣ) (v : V) : OpenRing d →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (f := raw d v) (den d) (by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.2
    have h := congrArg (fun f : Chart d →ₐ[R] R => f (den d)) (raw_augmentation d v)
    change (raw d v (den d)).fst = origin d (den d) at h
    rw [h,origin_den]
    exact isUnit_one)

theorem point_map (d : Rˣ) (v : V) (y : Chart d) :
    point d v (algebraMap (Chart d) (OpenRing d) y) = raw d v y := by
  rw [point,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]

theorem point_parameter (d : Rˣ) (v : V) :
    point d v (localT d) = TrivSqZeroExt.inr v :=
  (point_map d v _).trans (raw_parameter d v)

theorem point_ordinate (d : Rˣ) (v : V) : point d v (localZ d) = 0 :=
  (point_map d v _).trans (raw_ordinate d v)

theorem ext_local (d : Rˣ) {f g : OpenRing d →ₐ[R] S}
    (ht : f (localT d) = g (localT d)) (hz : f (localZ d) = g (localZ d)) : f = g := by
  let i := IsScalarTower.toAlgHom R (Chart d) (OpenRing d)
  have he : f.comp i = g.comp i := by
    apply Ideal.Quotient.algHom_ext R
    apply MvPolynomial.algHom_ext
    intro j
    fin_cases j
    · exact ht
    · exact hz
  have hbase (y : Chart d) :
      f (algebraMap (Chart d) (OpenRing d) y) = g (algebraMap (Chart d) (OpenRing d) y) :=
    congrArg (fun j : Chart d →ₐ[R] S => j y) he
  apply AlgHom.ext
  intro y
  obtain ⟨⟨a,b⟩,hab⟩ := IsLocalization.surj (Submonoid.powers (den d)) y
  have h₁ := congrArg f hab
  have h₂ := congrArg g hab
  rw [map_mul,hbase,hbase] at h₁
  rw [map_mul] at h₂
  have hu : IsUnit (g (algebraMap (Chart d) (OpenRing d) (b : Chart d))) :=
    (IsLocalization.map_units (OpenRing d) b).map g
  exact hu.mul_right_cancel (h₁.trans h₂.symm)

/-- Every actual algebra map reducing to the actual identity over an
arbitrary square-zero module is this exact chart point. The proof uses
the full scheme-theoretic ideal equality, not reduced points. -/
theorem exact_chart_point (d : Rˣ) (f : OpenRing d →ₐ[R] S)
    (h : fst.comp f = augmentation d) :
    ∃! v : V, f = point d v := by
  let v := (f (localT d)).snd
  have ht : (f (localT d)).fst = 0 := by
    have h0 := congrArg (fun F : OpenRing d →ₐ[R] R => F (localT d)) h
    change (f (localT d)).fst = augmentation d (localT d) at h0
    exact h0.trans ((augmentation_map d _).trans (origin_parameter d))
  have hT : f (localT d) = TrivSqZeroExt.inr v := TrivSqZeroExt.ext ht rfl
  have hZ : f (localZ d) = 0 := by
    let c := algebraMap (Chart d) (OpenRing d) (factor d)
    have hu : IsUnit c := IsLocalization.Away.isUnit_of_dvd (den d)
      (dvd_mul_left (factor d) (presentation d).jacobian)
    have hq : localZ d * c = (localT d)^3 := by
      simpa only [map_mul,map_pow] using
        congrArg (algebraMap (Chart d) (OpenRing d)) (equation_factored d)
    have hq' := congrArg f hq
    have h2 : (TrivSqZeroExt.inr v : S)^2 = 0 := (pow_two _).trans (TrivSqZeroExt.inr_mul_inr R v v)
    have h3 : (TrivSqZeroExt.inr v : S)^3 = 0 := by
      rw [show (3:ℕ) = 2+1 by decide,pow_succ,h2,zero_mul]
    rw [map_mul,map_pow,hT,h3,← zero_mul (f c)] at hq'
    exact (hu.map f).mul_right_cancel hq'
  refine ⟨v,ext_local d (hT.trans (point_parameter d v).symm)
    (hZ.trans (point_ordinate d v).symm),?_⟩
  intro w hw
  have hh := congrArg (fun F : OpenRing d →ₐ[R] S => F (localT d)) hw
  exact TrivSqZeroExt.inr_injective ((point_parameter d w).symm.trans (hh.symm.trans hT))

end SelectedGeneralizedInfinityActualJets318

#print axioms SelectedGeneralizedInfinityActualJets318.point_parameter
#print axioms SelectedGeneralizedInfinityActualJets318.exact_chart_point
