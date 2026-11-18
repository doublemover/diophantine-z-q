module
public import OriginalPrimeThreeCotangentIndependence318
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public section
noncomputable section
namespace OriginalPrimeThreeLocalizedCotangent318
open OriginalPrimeThreeFirstOrderPoint318
open OriginalPrimeThreeCotangentIndependence318

/-- The literal local ring of the actual normalized finite chart at the
constructed maximal ideal, not a surrogate completed or coefficient ring. -/
abbrev PointRing := Localization.AtPrime pointIdeal

theorem point_units (s : pointIdeal.primeCompl) :
    IsUnit (normalizedPoint s) := by
  apply IsUnit.mk0
  intro h
  exact s.property (RingHom.mem_ker.mpr h)

theorem tangent_units (j : Fin 3) (s : pointIdeal.primeCompl) :
    IsUnit (tangentLift j s) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  change IsUnit ((normalizedLift (fun i => if i = j then 1 else 0) s).fst)
  rw [normalizedLift_fst]
  exact point_units s

@[expose] def localPoint : PointRing →+* K :=
  IsLocalization.lift (S := PointRing) point_units
@[expose] def localTangentLift (j : Fin 3) : PointRing →+* D :=
  IsLocalization.lift (S := PointRing) (tangent_units j)

@[simp] theorem localPoint_on_chart (z : Closure) :
    localPoint (algebraMap Closure PointRing z) = normalizedPoint z :=
  IsLocalization.lift_eq point_units z

@[simp] theorem localTangentLift_on_chart (j : Fin 3) (z : Closure) :
    localTangentLift j (algebraMap Closure PointRing z) = tangentLift j z :=
  IsLocalization.lift_eq (tangent_units j) z

theorem localTangentLift_fst (j : Fin 3) (z : PointRing) :
    (localTangentLift j z).fst = localPoint z := by
  have h : projection.comp (localTangentLift j) = localPoint := by
    apply IsLocalization.ringHom_ext pointIdeal.primeCompl
    apply RingHom.ext
    intro a
    change (localTangentLift j (algebraMap Closure PointRing a)).fst =
      localPoint (algebraMap Closure PointRing a)
    rw [localTangentLift_on_chart, localPoint_on_chart]
    exact normalizedLift_fst _ a
  exact RingHom.congr_fun h z

theorem localPoint_surjective : Function.Surjective localPoint := by
  intro z
  obtain ⟨a, ha⟩ := normalizedPoint_surjective z
  exact ⟨algebraMap Closure PointRing a, (localPoint_on_chart a).trans ha⟩

theorem localPoint_kernel : RingHom.ker localPoint = IsLocalRing.maximalIdeal PointRing :=
  IsLocalRing.ker_eq_maximalIdeal localPoint localPoint_surjective

@[expose] def localRoot (i : Fin 3) : PointRing :=
  algebraMap Closure PointRing (normalizedRoot i)

theorem localTangentLift_root (j i : Fin 3) :
    localTangentLift j (localRoot i) =
      TrivSqZeroExt.inr (if i = j then (1 : K) else 0) := by
  rw [localRoot, localTangentLift_on_chart, tangentLift_root]

theorem localRoot_mem_maximal (i : Fin 3) :
    localRoot i ∈ IsLocalRing.maximalIdeal PointRing := by
  rw [← localPoint_kernel]
  exact DualNumberCotangentCertificate318.root_mem_kernel localPoint localTangentLift
    localTangentLift_fst localRoot localTangentLift_root i

@[expose] def localCotangentClasses (i : Fin 3) : IsLocalRing.CotangentSpace PointRing :=
  cotangentClasses (IsLocalRing.maximalIdeal PointRing) localRoot localRoot_mem_maximal i

/-- These are independent in the local ring's actual cotangent space
over its actual residue field. All localized coefficients are covered. -/
theorem local_cotangent_linearIndependent :
    LinearIndependent (IsLocalRing.ResidueField PointRing) localCotangentClasses := by
  apply classes_linearIndependent (IsLocalRing.maximalIdeal PointRing)
    localRoot localRoot_mem_maximal
  intro a ha i
  rw [← localPoint_kernel] at ha ⊢
  exact RingHom.mem_ker.mpr
    (DualNumberCotangentCertificate318.independent_mod_square localPoint localTangentLift
      localTangentLift_fst localRoot localTangentLift_root a ha i)

local instance closureNoetherian : IsNoetherianRing Closure :=
  OriginalIntegerFiniteClosure318.closure_noetherian OriginalPrimeThreeActualQuotient318.twist
instance pointRingNoetherian : IsNoetherianRing PointRing :=
  IsLocalization.isNoetherianRing pointIdeal.primeCompl PointRing inferInstance

theorem local_cotangent_finrank_ge_three :
    3 ≤ Module.finrank (IsLocalRing.ResidueField PointRing)
      (IsLocalRing.CotangentSpace PointRing) := by
  simpa only [Fintype.card_fin] using local_cotangent_linearIndependent.fintype_card_le_finrank

end OriginalPrimeThreeLocalizedCotangent318
