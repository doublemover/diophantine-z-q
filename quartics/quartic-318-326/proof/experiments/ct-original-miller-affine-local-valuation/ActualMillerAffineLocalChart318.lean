module
public import ActualMillerAffineNormIdeal318
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
import all ActualMillerRegularEvaluation318
import all ActualTwoDescentAffineChartCoordinates318
import all ActualTwoDescentEllipticModel318
public section
noncomputable section

namespace ActualMillerAffineLocalChart318

open Polynomial
open ActualTwoDescentEllipticModel318 ActualTwoDescentAffineChartCoordinates318
open ActualMillerRegularEvaluation318
open WeierstrassCurve.Affine.CoordinateRing (XYIdeal YClass XClass_ne_zero YClass_ne_zero)

variable {K : Type*} [Field K] [CharZero K]

def affineYDiff (n v : K) : AffineChart n := affineY n - affineCoefficient n v
abbrev pointIdeal (n u v : K) : Ideal (AffineChart n) := XYIdeal (curve n).toAffine u (C v)

theorem point_ideal_generators (n u v : K) :
    pointIdeal n u v = Ideal.span {vertical n u, affineYDiff n v} := by
  simp only [pointIdeal, XYIdeal, YClass, affineYDiff, map_sub, vertical] <;> rfl

theorem point_ideal_kernel (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    pointIdeal n u v = RingHom.ker (affineEval n u v hR) := by
  let q : AffineChart n →+* AffineChart n ⧸ pointIdeal n u v :=
    Ideal.Quotient.mk (pointIdeal n u v)
  have hX : q (vertical n u) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by
    rw [point_ideal_generators]
    exact Ideal.subset_span (by simp))
  have hY : q (affineYDiff n v) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (by
    rw [point_ideal_generators]
    exact Ideal.subset_span (by simp))
  have hcomp : q = (q.comp (affineCoefficient n)).comp (affineEval n u v hR) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · apply RingHom.ext
        intro c
        change q (affineCoefficient n c) =
          q (affineCoefficient n (affineEval n u v hR (affineCoefficient n c)))
        rw [affineEval_const]
      · change q (affineX n) = q (affineCoefficient n (affineEval n u v hR (affineX n)))
        rw [affineEval_x]
        exact sub_eq_zero.mp (by simpa only [vertical_coordinates, map_sub] using hX)
    · change q (affineY n) = q (affineCoefficient n (affineEval n u v hR (affineY n)))
      rw [affineEval_y]
      exact sub_eq_zero.mp (by simpa only [affineYDiff, map_sub] using hY)
  refine le_antisymm ?_ ?_
  · rw [point_ideal_generators]
    apply Ideal.span_le.mpr
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | hw
    · change affineEval n u v hR (vertical n u) = 0
      rw [affineEval_vertical, sub_self]
    · rcases Set.mem_singleton_iff.mp hw with rfl
      change affineEval n u v hR (affineYDiff n v) = 0
      simp only [affineYDiff, map_sub, affineEval_y, affineEval_const, sub_self]
  · intro w hw
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q w = 0
    change affineEval n u v hR w = 0 at hw
    rw [hcomp]
    change q (affineCoefficient n (affineEval n u v hR w)) = 0
    rw [hw, map_zero, map_zero]

abbrev pointKernel (n u v : K) (hR : (curve n).toAffine.Equation u v) :=
  RingHom.ker (affineEval n u v hR)

instance pointKernel_prime (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    (pointKernel n u v hR).IsPrime := RingHom.ker_isPrime _

abbrev AffineLocal (n u v : K) (hR : (curve n).toAffine.Equation u v) :=
  Localization.AtPrime (pointKernel n u v hR)

abbrev affineLocalMap (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    AffineChart n →+* AffineLocal n u v hR := algebraMap _ _

instance affineLocal_domain (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    IsDomain (AffineLocal n u v hR) :=
  IsLocalization.isDomain_of_local_atPrime (pointKernel_prime n u v hR)

theorem affineLocal_injective (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    Function.Injective (affineLocalMap n u v hR) :=
  IsLocalization.injective (AffineLocal n u v hR) (pointKernel n u v hR).primeCompl_le_nonZeroDivisors

theorem local_unit_of_nonzero_value (n u v : K) (hR : (curve n).toAffine.Equation u v)
    (d : AffineChart n) (hd : affineEval n u v hR d ≠ 0) :
    IsUnit (affineLocalMap n u v hR d) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff _ (pointKernel n u v hR) d).mpr hd

theorem map_point_ideal_self (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    Ideal.map (affineLocalMap n u v hR) (pointIdeal n u v) =
      IsLocalRing.maximalIdeal (AffineLocal n u v hR) := by
  rw [point_ideal_kernel n u v hR]
  exact IsLocalization.AtPrime.map_eq_maximalIdeal (pointKernel n u v hR) (AffineLocal n u v hR)

theorem map_point_ideal_other (n u v x y : K) (hR : (curve n).toAffine.Equation u v)
    (hne : ¬(x = u ∧ y = v)) :
    Ideal.map (affineLocalMap n u v hR) (pointIdeal n x y) = ⊤ := by
  let f := affineLocalMap n u v hR
  have htop {d : AffineChart n} (hd : d ∈ pointIdeal n x y)
      (hu : IsUnit (f d)) : Ideal.map f (pointIdeal n x y) = ⊤ := by
    exact (Ideal.map f (pointIdeal n x y)).eq_top_of_isUnit_mem (Ideal.mem_map_of_mem f hd) hu
  by_cases hx : x = u
  · have hy : y ≠ v := fun he => hne ⟨hx, he⟩
    apply htop (d := affineYDiff n y)
    · rw [point_ideal_generators]
      exact Ideal.subset_span (by simp)
    · apply local_unit_of_nonzero_value
      simpa only [affineYDiff, map_sub, affineEval_y, affineEval_const] using sub_ne_zero.mpr hy.symm
  · apply htop (d := vertical n x)
    · rw [point_ideal_generators]
      exact Ideal.subset_span (by simp)
    · apply local_unit_of_nonzero_value
      rw [affineEval_vertical]
      exact sub_ne_zero.mpr hx.symm

/-- A concrete affine local parameter is produced at every smooth
original affine point: X-u for v≠0 and Y-v for v=0. -/
def cubicCofactor (n u : K) : AffineChart n :=
  (affineX n)^2 + affineCoefficient n (u + 2*n) * affineX n +
    affineCoefficient n (u^2 + 2*n*u - 3*n^2)

private theorem y_diff_class (n v : K) :
    affineYDiff n v = YClass (curve n).toAffine (C v) := by
  simp only [affineYDiff, YClass, map_sub] <;> rfl

theorem affine_cubic_factored (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    affineYDiff n v * (affineY n + affineCoefficient n v) =
      vertical n u * cubicCofactor n u := by
  have hR' : v^2 - u^3 - 2*n*u^2 + 3*n^2*u = 0 := by
    linear_combination (curve_equation n u v).mp hR
  have hconst := congrArg (affineCoefficient n) hR'
  simp only [map_sub, map_add, map_pow, map_mul, map_ofNat, map_zero] at hconst
  rw [affineYDiff, vertical_coordinates, cubicCofactor]
  simp only [map_add, map_sub, map_pow, map_mul, map_ofNat]
  linear_combination actual_affine_cubic n - hconst

@[simp] theorem eval_cubicCofactor (n u v : K) (hR : (curve n).toAffine.Equation u v) :
    affineEval n u v hR (cubicCofactor n u) = 3*u^2 + 4*n*u - 3*n^2 := by
  simp only [cubicCofactor, map_add, map_pow, map_mul, affineEval_x, affineEval_const]
  ring

private theorem dvd_from_unit_factor {A : Type*} [CommRing A] {x y w s : A}
    (hs : IsUnit s) (h : y*s = x*w) : x ∣ y := by
  obtain ⟨e, he⟩ := hs
  refine ⟨w * (↑(e⁻¹) : A), ?_⟩
  calc
    y = (y*s)*(↑(e⁻¹) : A) := by rw [← he, mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [h, mul_assoc]

theorem actual_affine_local_principal (n u v : K) (hn : n ≠ 0)
    (hR : (curve n).toAffine.Equation u v) :
    ∃ π : AffineLocal n u v hR, π ≠ 0 ∧
      IsLocalRing.maximalIdeal (AffineLocal n u v hR) = Ideal.span {π} := by
  let f := affineLocalMap n u v hR
  let d := f (vertical n u)
  let e := f (affineYDiff n v)
  have hmax : IsLocalRing.maximalIdeal (AffineLocal n u v hR) = Ideal.span {d,e} := by
    rw [← map_point_ideal_self n u v hR, point_ideal_generators, Ideal.map_span, Set.image_pair]
  have hfac : e * f (affineY n + affineCoefficient n v) = d * f (cubicCofactor n u) := by
    simpa only [map_mul] using congrArg f (affine_cubic_factored n u v hR)
  by_cases hv : v = 0
  · have hs : (curve n).toAffine.Nonsingular u v :=
      curve_nonsingular n u v hn ((curve_equation n u v).mp hR)
    have hder : 3*u^2 + 4*n*u - 3*n^2 ≠ 0 := by
      have h := ((curve n).toAffine.nonsingular_iff' u v).mp hs
      rcases h.2 with h | h
      · intro hzero
        apply h
        change (0 : K)*v - (3*u^2 + 2*(2*n)*u + (-3*n^2)) = 0
        linear_combination -hzero
      · simp [curve, hv] at h
    have hq : IsUnit (f (cubicCofactor n u)) :=
      local_unit_of_nonzero_value n u v hR _ (by rw [eval_cubicCofactor]; exact hder)
    have hdiv : e ∣ d := dvd_from_unit_factor hq hfac.symm
    refine ⟨e, ?_, ?_⟩
    · intro he
      have hb : affineYDiff n v = 0 := affineLocal_injective n u v hR
        (by simpa only [map_zero] using he)
      rw [y_diff_class] at hb
      exact YClass_ne_zero _ hb
    · rw [hmax, Set.pair_comm]
      exact Ideal.span_pair_eq_span_left_iff_dvd.mpr hdiv
  · have hq : IsUnit (f (affineY n + affineCoefficient n v)) := by
      apply local_unit_of_nonzero_value
      simp only [map_add, affineEval_y, affineEval_const, ← two_mul]
      exact mul_ne_zero two_ne_zero hv
    have hdiv : d ∣ e := dvd_from_unit_factor hq hfac
    refine ⟨d, ?_, ?_⟩
    · intro hd
      have hb : vertical n u = 0 := affineLocal_injective n u v hR
        (by simpa only [map_zero] using hd)
      exact XClass_ne_zero _ hb
    · rw [hmax]
      exact Ideal.span_pair_eq_span_left_iff_dvd.mpr hdiv

theorem actual_affine_local_DVR (n u v : K) (hn : n ≠ 0)
    (hR : (curve n).toAffine.Equation u v) :
    IsDiscreteValuationRing (AffineLocal n u v hR) := by
  letI : IsNoetherianRing (AffineChart n) :=
    isNoetherianRing_of_surjective (Polynomial (Polynomial K)) (AffineChart n)
      (AdjoinRoot.mk (curve n).toAffine.polynomial) AdjoinRoot.mk_surjective
  letI : IsNoetherianRing (AffineLocal n u v hR) :=
    IsLocalization.isNoetherianRing (pointKernel n u v hR).primeCompl (AffineLocal n u v hR) inferInstance
  obtain ⟨π, hπ, hmax⟩ := actual_affine_local_principal n u v hn hR
  have hne : IsLocalRing.maximalIdeal (AffineLocal n u v hR) ≠ ⊥ := by
    rw [hmax, Ideal.span_singleton_eq_bot]
    exact hπ
  have hf : ¬IsField (AffineLocal n u v hR) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hne
  have hp : (IsLocalRing.maximalIdeal (AffineLocal n u v hR)).IsPrincipal := by
    rw [hmax]
    infer_instance
  exact ((IsDiscreteValuationRing.TFAE (AffineLocal n u v hR) hf).out 5 1).mp hp

end ActualMillerAffineLocalChart318
