module
public import OriginalMarkedBranchMap318
public import OriginalBranchEvaluationExt318
public section
noncomputable section
namespace OriginalMarkedBranchEvaluation318
open Polynomial
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Algebra ℚ A]
  (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j,RationalContactPoint318.parameters c t j≠0)
  (T : A) (r : Fin 4 → A)
  (hr : ∀ j,(r j)^2=algebraMap ℚ A (c j : ℚ)*(T-algebraMap ℚ A (LinearContactSquareclass318.contacts j)))
  (hu : ∀ j,IsUnit (r j))
  (e : A →ₐ[ℚ] RationalContactPoint318.PointField c t)
  (hT : e T=algebraMap ℚ (RationalContactPoint318.PointField c t) t)
  (hroot : ∀ j,e (r j)=RationalFourRootFiber318.root (RationalContactPoint318.parameters c t) j)

include hT in
theorem polynomial_square : e.toRingHom.comp (OriginalMarkedBranchMap318.sourceScalar T)=
    (algebraMap ℚ (RationalContactPoint318.PointField c t)).comp (Polynomial.aeval t).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro q
    change e (Polynomial.eval₂ (algebraMap ℚ A) T (C q))=_
    rw [Polynomial.eval₂_C,e.commutes]
    change algebraMap ℚ _ q=algebraMap ℚ _ (Polynomial.aeval t (C q))
    rw [Polynomial.aeval_C]
  · change e (Polynomial.eval₂ (algebraMap ℚ A) T X)=_
    rw [Polynomial.eval₂_X,hT]
    change algebraMap ℚ _ t=algebraMap ℚ _ (Polynomial.aeval t X)
    rw [Polynomial.aeval_X]

/-- Equality of FULL localized original branch evaluations, including
all original signed roots, not merely equality of the two section ratios. -/
include hT hroot in
theorem branch_point (i : Fin 4) :
    e.toRingHom.comp (OriginalMarkedBranchMap318.branchMap c T r hr hu i).toRingHom=
      ContactBranchPoint318.branchPoint c t hn i := by
  apply OriginalBranchEvaluationExt318.eq_original c t hn i
  · intro p
    change e (OriginalMarkedBranchMap318.branchRingMap c T r hr hu i (algebraMap _ _ (algebraMap ℚ[X] _ p)))=_
    rw [OriginalMarkedBranchMap318.branchRingMap_base,OriginalMarkedBranchMap318.sourceMap_polynomial]
    exact RingHom.congr_fun (polynomial_square c t T e hT) p
  · intro j
    change e (OriginalMarkedBranchMap318.branchRingMap c T r hr hu i (algebraMap _ _ (FourRootOrderSigns318.generator _ j)))=_
    rw [OriginalMarkedBranchMap318.branchRingMap_base,OriginalMarkedBranchMap318.sourceMap_generator]
    exact hroot j
end OriginalMarkedBranchEvaluation318
