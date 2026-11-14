module
public import ContactBranchPoint318
public import ContactBicanonicalCoefficients318
public import IntegralRootPointMaps318
public section
noncomputable section
namespace OriginalBranchEvaluationExt318
open Polynomial
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j,RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
  (f : ContactBicanonicalCoefficients318.BranchRing c i →+* RationalContactPoint318.PointField c t)

/-- Full equality on the original branch ring follows from its ACTUAL
polynomial base map and all four original signed generators. -/
theorem eq_original
    (hpoly : ∀ p : ℚ[X],f (algebraMap (ContactKummerOrder318.SourceOrder c)
      (ContactBicanonicalCoefficients318.BranchRing c i)
        (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) p))=
          algebraMap ℚ (RationalContactPoint318.PointField c t) (Polynomial.aeval t p))
    (hroot : ∀ j,f (algebraMap (ContactKummerOrder318.SourceOrder c)
      (ContactBicanonicalCoefficients318.BranchRing c i)
        (FourRootOrderSigns318.generator (ContactKummerOrder318.coefficient c) j))=
          RationalFourRootFiber318.root (RationalContactPoint318.parameters c t) j) :
    f=ContactBranchPoint318.branchPoint c t hn i := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (SourceDenominatorCover318.denominator c i))
  apply IntegralRootPointMaps318.four_ringHom_ext
  · ext p
    change f (algebraMap _ _ (algebraMap ℚ[X] _ p))=
      ContactBranchPoint318.branchPoint c t hn i (algebraMap _ _ (algebraMap ℚ[X] _ p))
    rw [hpoly,ContactBranchPoint318.branchPoint_polynomial]
  · intro j
    change f (algebraMap _ _ (FourRootOrderSigns318.generator _ j))=
      ContactBranchPoint318.branchPoint c t hn i (algebraMap _ _ (FourRootOrderSigns318.generator _ j))
    rw [hroot,ContactBranchPoint318.branchPoint_algebraMap,
      RationalContactPoint318.sourcePoint_generator]
end OriginalBranchEvaluationExt318
