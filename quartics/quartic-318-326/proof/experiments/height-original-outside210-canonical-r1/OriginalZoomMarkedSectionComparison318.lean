module
public import OriginalFiniteZoomBranchMap318
public import OriginalReciprocalZoomBranchMap318
public section
noncomputable section
namespace OriginalZoomMarkedSectionComparison318
open IntegralContactZoomCoefficients318
open scoped TensorProduct
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] [CharZero K]
  (c : Fin 4 → ℚˣ) (d a : Fin 4 → K) (t : K) (m : Mode) (y s : Fin 4 → K)
  (ha : a=fun i => algebraMap ℚ K (LinearContactSquareclass318.contacts i))
  (hs : ∀ i,s i≠0) (hc : ∀ i,algebraMap ℚ K (c i : ℚ)=d i*(s i)^2)
  (hy : ∀ i,(y i)^2=IntegralQuadraticPointZoom318.value (alpha d a m) d (gamma d a m) t i)
  (hn : ∀ i,y i≠0)
@[expose] def branchMap (i : Fin 4) : ContactBicanonicalCoefficients318.BranchRing c i →ₐ[ℚ] Chart d a t m := by
  subst a
  cases m with
  | finite => exact OriginalFiniteZoomBranchMap318.branchMap c d t y s hs hc hy hn i
  | reciprocal => exact OriginalReciprocalZoomBranchMap318.branchMap c d t y s hs hc hy hn i

@[expose] def originalSection0 (i : Fin 4) : Omega d a t m ⊗[Chart d a t m] Omega d a t m :=
  ContactBicanonicalGenericPullback318.branchImage c i (branchMap c d a t m y s ha hs hc hy hn i)
@[expose] def originalSection1 (i : Fin 4) : Omega d a t m ⊗[Chart d a t m] Omega d a t m :=
  branchMap c d a t m y s ha hs hc hy hn i (ContactBicanonicalCoefficients318.branchQ1 c i) •
    (KaehlerDifferential.D K _ (branchMap c d a t m y s ha hs hc hy hn i
      (ContactFrameNormalization318.sourceCoordinate c i)) ⊗ₜ[Chart d a t m]
      KaehlerDifferential.D K _ (branchMap c d a t m y s ha hs hc hy hn i
        (ContactFrameNormalization318.sourceCoordinate c i)))

theorem q0_identification (i : Fin 4) : section0 d a t m=originalSection0 c d a t m y s ha hs hc hy hn i := by
  subst a
  cases m with
  | finite => exact OriginalFiniteZoomBranchMap318.original_q0 c d t y s hs hc hy hn i
  | reciprocal => exact OriginalReciprocalZoomBranchMap318.original_q0 c d t y s hs hc hy hn i

theorem q1_identification (i : Fin 4) : section1 d a t m=originalSection1 c d a t m y s ha hs hc hy hn i := by
  subst a
  cases m with
  | finite =>
    exact ContactBicanonicalGenericPullback318.finite_original_q1 c i d
      (OriginalFiniteZoomBranchMap318.contacts (K:=K)) t y hy hn
      (OriginalFiniteZoomBranchMap318.branchMap c d t y s hs hc hy hn i)
      (OriginalFiniteZoomBranchMap318.branchMap_T c d t y s hs hc hy hn i)
      (OriginalFiniteZoomBranchMap318.branchMap_P c d t y s hs hc hy hn i)
  | reciprocal => exact OriginalReciprocalZoomBranchMap318.original_q1 c d t y s hs hc hy hn i
end OriginalZoomMarkedSectionComparison318
