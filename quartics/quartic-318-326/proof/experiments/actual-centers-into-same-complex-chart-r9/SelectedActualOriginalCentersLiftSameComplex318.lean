module

public import SelectedActualSameMarkedComplexCenter318
public import SelectedOriginalLiteralAtOne318
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Tactic.NormNum

public section
noncomputable section
open Polynomial
open scoped Polynomial TensorProduct
open SelectedOriginalLiteralAtOne318 SelectedOriginalLiteralScalarUniqueness318
open SelectedActualOriginalOrdinaryRootBaseComparison318
open SelectedActualSameMarkedComplexCenter318

namespace SelectedActualOriginalCentersLiftSameComplex318

variable (L : Type) [Field L] [CharZero L]

private abbrev baseAtOnePolynomial : ℚ[X] →+* L :=
  Polynomial.eval₂RingHom (algebraMap ℚ L) (1 : L)

private theorem rationalDenominatorUnit : IsUnit
    (baseAtOnePolynomial L SelectedOriginalRationalOrdinary318.denominator) := by
  apply isUnit_iff_ne_zero.mpr
  simp only [SelectedOriginalRationalOrdinary318.denominator, baseAtOnePolynomial,
    Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_sub,
    Polynomial.eval₂_X, Polynomial.eval₂_C, map_ofNat, one_mul]
  norm_num

def rationalAtOne : SelectedOriginalRationalOrdinary318.Base →+* L :=
  IsLocalization.Away.lift SelectedOriginalRationalOrdinary318.denominator (rationalDenominatorUnit L)

theorem rationalAtOne_j :
    rationalAtOne L SelectedOriginalRationalOrdinary318.jCoord = 1 := by
  unfold SelectedOriginalRationalOrdinary318.jCoord rationalAtOne
  rw [IsLocalization.Away.lift_eq]
  exact Polynomial.eval₂_X _ _

variable (M : ℕ) [NeZero M] (p : (OpenJModel318.Base M)[X])

theorem rationalAtOne_composite :
    (rationalAtOne L).comp (SelectedOriginalRationalOrdinary318.toRational M) = atOne L M := by
  apply over_original_j_eq
  change rationalAtOne L
    (SelectedOriginalRationalOrdinary318.toRational M (OpenJModel318.jCoord M)) =
      atOne L M (OpenJModel318.jCoord M)
  rw [SelectedOriginalRationalOrdinary318.toRational_j, rationalAtOne_j, atOne_j]

variable (f : AdjoinRoot p →+* L)
variable (hf : f (AdjoinRoot.of p (OpenJModel318.jCoord M)) = 1)

include hf in
private theorem f_base : f.comp (AdjoinRoot.of p) = atOne L M := by
  apply over_original_j_eq
  exact hf.trans (atOne_j L M).symm

include hf in
private theorem rational_root_eq_zero :
    (pQ M p).eval₂ (rationalAtOne L) (f (AdjoinRoot.root p)) = 0 := by
  unfold pQ
  rw [Polynomial.eval₂_map, rationalAtOne_composite L M, ← f_base L M p f hf]
  rw [← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

include hf in
/-- The original whole actual evaluation f at J=1 gives a uniquely
specified character of the already installed rational ordinary monic
quotient. Its root is exactly f applied to the original primitive x. -/
def rationalCenter : AdjoinRoot (pQ M p) →ₐ[ℚ] L :=
  { AdjoinRoot.lift (rationalAtOne L) (f (AdjoinRoot.root p)) (rational_root_eq_zero L M p f hf) with
    commutes' := RingHom.map_rat_algebraMap (AdjoinRoot.lift (rationalAtOne L)
      (f (AdjoinRoot.root p)) (rational_root_eq_zero L M p f hf)) }

theorem rational_center_is_original :
    (rationalCenter L M p f hf).toRingHom.comp
      (AdjoinRoot.map (SelectedOriginalRationalOrdinary318.toRational M) p (pQ M p) (dvd_refl _)) = f := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change rationalCenter L M p f hf
      (AdjoinRoot.map (SelectedOriginalRationalOrdinary318.toRational M) p (pQ M p)
        (dvd_refl _) (AdjoinRoot.of p a)) = f (AdjoinRoot.of p a)
    rw [AdjoinRoot.map_of]
    change AdjoinRoot.lift (rationalAtOne L) (f (AdjoinRoot.root p))
      (rational_root_eq_zero L M p f hf)
      (AdjoinRoot.of (pQ M p) (SelectedOriginalRationalOrdinary318.toRational M a)) =
      f (AdjoinRoot.of p a)
    rw [AdjoinRoot.lift_of]
    exact (RingHom.congr_fun (rationalAtOne_composite L M) a).trans
      (RingHom.congr_fun (f_base L M p f hf) a).symm
  · change rationalCenter L M p f hf
      (AdjoinRoot.map (SelectedOriginalRationalOrdinary318.toRational M) p (pQ M p)
        (dvd_refl _) (AdjoinRoot.root p)) = f (AdjoinRoot.root p)
    rw [AdjoinRoot.map_root]
    exact AdjoinRoot.lift_root (rational_root_eq_zero L M p f hf)

variable [Algebra L ℂ] [IsScalarTower ℚ L ℂ]

include hf in
/-- Under the actual specified embedding L→C, the entire center chosen
in the original arithmetic evaluation fiber has the same x and the
literal same J=1 in the installed complex ordinary monic chart. -/
theorem original_center_retained :
    ∃ χ : AdjoinRoot (pC M p) →ₐ[ℂ] ℂ,
      χ (AdjoinRoot.root (pC M p)) = algebraMap L ℂ (f (AdjoinRoot.root p)) ∧
      χ (AdjoinRoot.of (pC M p) SelectedComplexOrdinaryBase318.jCoord) = 1 := by
  let e := rationalCenter L M p f hf
  have hx : e (AdjoinRoot.root (pQ M p)) = f (AdjoinRoot.root p) :=
    AdjoinRoot.lift_root (rational_root_eq_zero L M p f hf)
  have hj : e (AdjoinRoot.of (pQ M p) SelectedOriginalRationalOrdinary318.jCoord) = 1 :=
    (AdjoinRoot.lift_of (rational_root_eq_zero L M p f hf)).trans (rationalAtOne_j L)
  refine ⟨complexCenter M p L e,?_ ,center_retains_literal_J_one M p L e hj⟩
  exact (center_retains_original_abscissa M p L e).trans (congrArg (algebraMap L ℂ) hx)

end SelectedActualOriginalCentersLiftSameComplex318

#print axioms SelectedActualOriginalCentersLiftSameComplex318.rational_center_is_original
#print axioms SelectedActualOriginalCentersLiftSameComplex318.original_center_retained
