module
public import ContactProjectiveParameterStructure318
public section
noncomputable section
namespace ContactProjectiveParameterIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (a b : Chart)
/-- The actual avoidance overlap is the categorical intersection of the
two original quotient charts inside the new glued parameter scheme. -/
lemma cartesian : IsPullback (parameterOpen c a b n).ι
    ((ContactQuotientOverlapSchemeIso318.iso c a b n).hom ≫ (parameterOpen c b a n).ι)
    (ContactProjectiveQuotientParameter318.into c n a) (ContactProjectiveQuotientParameter318.into c n b) :=
  IsPullback.of_isLimit ((ContactProjectiveQuotientParameter318.data c n).vPullbackConeIsLimit a b)
end ContactProjectiveParameterIntersection318
