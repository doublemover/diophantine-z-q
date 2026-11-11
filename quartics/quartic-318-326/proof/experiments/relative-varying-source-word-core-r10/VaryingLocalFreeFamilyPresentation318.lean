module
public import VaryingGlobalFamilyPresentation318
public import VaryingLocalFreeFamilyRecovery318
public section
noncomputable section
namespace VaryingLocalFreeFamilyPresentation318
open AlgebraicGeometry CategoryTheory
open VaryingLocalFreeQuotientEquiv318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
instance pointPresentation (x : VaryingParameterPoint318.Point R A ι S) :
    LocallyOfFinitePresentation (VaryingParameterPointFamily318.projection R A ι S x) :=
  inferInstanceAs (LocallyOfFinitePresentation (CategoryTheory.Limits.pullback.snd _ _))
/-- Finite presentation of the LITERAL original quotient projection,
transported through the actual universal-family comparison. -/
instance presentation (I : LocalIdeal R A ι S) :
    LocallyOfFinitePresentation (VaryingWholeIdealFamily318.projection R A S I.val) := by
  rw [← VaryingLocalFreeFamilyRecovery318.comparison_projection R A ι S I]
  infer_instance
end VaryingLocalFreeFamilyPresentation318
