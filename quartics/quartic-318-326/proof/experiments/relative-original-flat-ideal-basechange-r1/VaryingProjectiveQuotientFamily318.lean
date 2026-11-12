module
public import VaryingProjectiveQuotientNaturality318
public section
noncomputable section
namespace VaryingProjectiveQuotientFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open VaryingProjectiveQuotientEquiv318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
  (I : ProjectiveIdeal R A ι S)
/-- The module-theoretically classified input has the SAME literal
original quotient family as the pullback of the actual universal family. -/
@[expose] def comparison : VaryingWholeIdealFamily318.family R A S I.val ≅
    VaryingParameterPointFamily318.family R A ι S (equivalence R A ι S I) :=
  VaryingLocalFreeFamilyRecovery318.comparison R A ι S (toLocal R A ι S I)
@[reassoc] lemma comparison_into : (comparison R A ι S I).hom ≫
    VaryingParameterPointFamily318.intoSource R A ι S (equivalence R A ι S I)=
      VaryingWholeIdealFamily318.into R A S I.val :=
  VaryingLocalFreeFamilyRecovery318.comparison_into R A ι S (toLocal R A ι S I)
lemma cartesian : IsPullback
    ((comparison R A ι S I).hom ≫ VaryingParameterPointFamily318.intoFamily R A ι S (equivalence R A ι S I))
    (VaryingWholeIdealFamily318.projection R A S I.val)
    (VaryingWordGlobalFamilyProjection318.projection R A ι) (equivalence R A ι S I).val :=
  VaryingLocalFreeFamilyRecovery318.cartesian R A ι S (toLocal R A ι S I)
end VaryingProjectiveQuotientFamily318
