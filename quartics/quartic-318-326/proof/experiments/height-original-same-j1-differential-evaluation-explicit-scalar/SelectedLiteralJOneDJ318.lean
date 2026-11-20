module
public import OpenJModel318
public import SelectedNormalizedEtaleDJ318
public import Mathlib.Analysis.Complex.Basic
public section
noncomputable section
open Polynomial KaehlerDifferential SelectedNormalizedEtaleDJ318
open scoped TensorProduct

namespace SelectedLiteralJOneDJ318

variable (M : ℕ)

abbrev R := OpenJModel318.Base M
variable (p : (R M)[X])
abbrev S := AdjoinRoot p
abbrev Rat := ℚ ⊗[ℤ] (S M p)
abbrev Cpx := ℂ ⊗[ℤ] (S M p)
abbrev j := algebraMap (R M) (S M p) (OpenJModel318.jCoord M)
abbrev jRat := (1 : ℚ) ⊗ₜ[ℤ] j M p
abbrev jCpx := (1 : ℂ) ⊗ₜ[ℤ] j M p

/-- The genuine base derivative is that of the variable in the literal
localization by (6M)j(j-1728), not a chart parameter supplied by hand. -/
@[expose] def baseFrame : KaehlerDifferential ℤ (R M) ≃ₗ[R M] R M := by
  letI : Algebra.Etale (ℤ[X]) (R M) :=
    Algebra.Etale.of_isLocalizationAway (OpenJModel318.denominator M)
  exact etaleFrame (polynomialEquiv ℤ)

theorem baseFrame_j : baseFrame M (D ℤ (R M) (OpenJModel318.jCoord M)) = 1 := by
  letI : Algebra.Etale (ℤ[X]) (R M) :=
    Algebra.Etale.of_isLocalizationAway (OpenJModel318.denominator M)
  change etaleFrame (polynomialEquiv ℤ) (D ℤ (R M) (algebraMap (ℤ[X]) (R M) X)) = 1
  rw [etaleFrame_D,polynomialEquiv_D,derivative_X,map_one]

/-- Transfer the derivative unit from the actual fixed-coordinate chart.
The root equality is essential: no unrelated root can be substituted. -/
theorem root_derivative_isUnit {A : Type*} [CommRing A] [Algebra (R M) A]
    (e : S M p ≃ₐ[R M] A) (x : A) (hx : e (AdjoinRoot.root p) = x)
    (h : IsUnit (aeval x p.derivative)) : IsUnit (AdjoinRoot.mk p p.derivative) := by
  have hm : e (AdjoinRoot.mk p p.derivative) = aeval x p.derivative := by
    rw [← AdjoinRoot.aeval_eq,← Polynomial.aeval_algHom_apply,hx]
  have hu : IsUnit (e (AdjoinRoot.mk p p.derivative)) := by rw [hm]; exact h
  have hh := hu.map e.symm.toRingHom
  change IsUnit (e.symm (e (AdjoinRoot.mk p p.derivative))) at hh
  rwa [AlgEquiv.symm_apply_apply] at hh

variable (hp : p.Monic) (hu : IsUnit (AdjoinRoot.mk p p.derivative))

/-- Normalized differential coefficient on the actual monic root chart. -/
@[expose] def rootFrame : KaehlerDifferential ℤ (S M p) ≃ₗ[S M p] S M p := by
  letI : Algebra.Etale (R M) (S M p) := etale_of_derivative p hp hu
  exact etaleFrame (baseFrame M)

theorem rootFrame_base (r : R M) :
    rootFrame M p hp hu (D ℤ (S M p) (algebraMap (R M) (S M p) r)) =
      algebraMap (R M) (S M p) (baseFrame M (D ℤ (R M) r)) := by
  letI : Algebra.Etale (R M) (S M p) := etale_of_derivative p hp hu
  exact etaleFrame_D (baseFrame M) r

theorem rootFrame_j : rootFrame M p hp hu (D ℤ (S M p) (j M p)) = 1 := by
  rw [j,rootFrame_base,baseFrame_j,map_one]

@[expose] def rationalFrame : KaehlerDifferential ℚ (Rat M p) ≃ₗ[Rat M p] Rat M p :=
  tensorFrame (F := ℚ) (rootFrame M p hp hu)

@[expose] def complexFrame : KaehlerDifferential ℂ (Cpx M p) ≃ₗ[Cpx M p] Cpx M p :=
  tensorFrame (F := ℂ) (rootFrame M p hp hu)

theorem rationalFrame_j : rationalFrame M p hp hu (D ℚ (Rat M p) (jRat M p)) = 1 :=
  tensorFrame_normalized (rootFrame M p hp hu) (j M p) (rootFrame_j M p hp hu)

theorem complexFrame_j : complexFrame M p hp hu (D ℂ (Cpx M p) (jCpx M p)) = 1 :=
  tensorFrame_normalized (rootFrame M p hp hu) (j M p) (rootFrame_j M p hp hu)

theorem regular_coefficient (ω : KaehlerDifferential ℚ (Rat M p)) :
    ω = (rationalFrame M p hp hu ω) • D ℚ (Rat M p) (jRat M p) :=
  coefficient_spec _ _ (rationalFrame_j M p hp hu) ω

theorem regular_coefficient_iff (ω : KaehlerDifferential ℚ (Rat M p)) (a : Rat M p) :
    ω = a • D ℚ (Rat M p) (jRat M p) ↔ rationalFrame M p hp hu ω = a :=
  coefficient_iff _ _ (rationalFrame_j M p hp hu) ω a

/-- At any actual center point, evaluate the genuine regular coefficient
in its given residue field. There is no additional frame-choice scalar. -/
@[expose] def coefficientAt {L : Type*} [CommRing L] [Algebra ℚ L]
    (β : Rat M p →ₐ[ℚ] L) (ω : KaehlerDifferential ℚ (Rat M p)) : L :=
  β (rationalFrame M p hp hu ω)

theorem coefficientAt_dj {L : Type*} [CommRing L] [Algebra ℚ L]
    (β : Rat M p →ₐ[ℚ] L) (a : Rat M p) :
    coefficientAt M p hp hu β (a • D ℚ (Rat M p) (jRat M p)) = β a := by
  change β (rationalFrame M p hp hu (a • D ℚ (Rat M p) (jRat M p))) = β a
  rw [map_smul,rationalFrame_j,smul_eq_mul,mul_one]

section Local
variable {T : Type*} [CommRing T] [Algebra ℚ T] [Algebra (Rat M p) T]
variable [IsScalarTower ℚ (Rat M p) T]
variable (U : Submonoid (Rat M p)) [IsLocalization U T]

/-- The actual frame on further localizations of this chart, including
its local ring at the chosen j=1 center. -/
@[expose] def localFrame : KaehlerDifferential ℚ T ≃ₗ[T] T := by
  letI : Algebra.FormallyEtale (Rat M p) T := Algebra.FormallyEtale.of_isLocalization U
  exact etaleFrame (rationalFrame M p hp hu)

theorem localFrame_j :
    localFrame M p hp hu U (D ℚ T (algebraMap (Rat M p) T (jRat M p))) = 1 := by
  letI : Algebra.FormallyEtale (Rat M p) T := Algebra.FormallyEtale.of_isLocalization U
  change etaleFrame (rationalFrame M p hp hu) (D ℚ T (algebraMap (Rat M p) T (jRat M p))) = 1
  rw [etaleFrame_D,rationalFrame_j,map_one]

theorem local_coefficient (ω : KaehlerDifferential ℚ T) :
    ω = (localFrame M p hp hu U ω) • D ℚ T (algebraMap (Rat M p) T (jRat M p)) :=
  coefficient_spec _ _ (localFrame_j M p hp hu U) ω

end Local

/-- The true derivative in this frame. -/
@[expose] def delta : Derivation ℤ (S M p) (S M p) :=
  (rootFrame M p hp hu).toLinearMap.compDer (D ℤ (S M p))

theorem delta_j : delta M p hp hu (j M p) = 1 :=
  rootFrame_j M p hp hu

theorem delta_coefficient (a : R M) :
    delta M p hp hu (algebraMap (R M) (S M p) a) =
      algebraMap (R M) (S M p) (baseFrame M (D ℤ (R M) a)) :=
  rootFrame_base M p hp hu a

theorem actual_implicit_relation :
    AdjoinRoot.mk p p.derivative * delta M p hp hu (AdjoinRoot.root p) =
      -p.sum (fun n a => delta M p hp hu (algebraMap (R M) (S M p) a) * (AdjoinRoot.root p)^n) := by
  have h := implicit_relation (delta M p hp hu) (algebraMap (R M) (S M p))
    (AdjoinRoot.root p) p (AdjoinRoot.eval₂_root p)
  change aeval (AdjoinRoot.root p) p.derivative * delta M p hp hu (AdjoinRoot.root p) = _ at h
  rwa [AdjoinRoot.aeval_eq] at h

theorem actual_implicit_solve :
    delta M p hp hu (AdjoinRoot.root p) =
      (↑hu.unit⁻¹ : S M p) *
        (-p.sum (fun n a => delta M p hp hu (algebraMap (R M) (S M p) a) *
          (AdjoinRoot.root p)^n)) := by
  have hi : (↑hu.unit⁻¹ : S M p) * AdjoinRoot.mk p p.derivative = 1 := by
    rw [← hu.unit_spec]
    exact Units.inv_mul _
  calc
    _ = (↑hu.unit⁻¹ : S M p) *
        (AdjoinRoot.mk p p.derivative * delta M p hp hu (AdjoinRoot.root p)) := by
      rw [← mul_assoc,hi,one_mul]
    _ = _ := by rw [actual_implicit_relation]

end SelectedLiteralJOneDJ318

#print axioms SelectedLiteralJOneDJ318.regular_coefficient_iff
#print axioms SelectedLiteralJOneDJ318.local_coefficient
#print axioms SelectedLiteralJOneDJ318.actual_implicit_solve
