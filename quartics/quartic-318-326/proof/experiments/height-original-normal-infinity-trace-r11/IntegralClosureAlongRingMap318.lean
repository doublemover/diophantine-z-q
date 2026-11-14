module
public import NormalizationClosureChart318
public section
noncomputable section
namespace IntegralClosureAlongRingMap318
variable {P B : Type*} [CommRing P] [CommRing B] (f : P →+* B)

/-- Keep the chosen polynomial scalar in the integral-closure TYPE.
In particular finite and reciprocal closures cannot silently share the
canonical polynomial action on the same ambient source carrier. -/
abbrev Closure := letI := f.toAlgebra; integralClosure P B

@[expose] def scalar : P →+* Closure f := by
  letI := f.toAlgebra
  exact algebraMap P (integralClosure P B)

@[expose] def inclusion : Closure f →+* B := by
  letI := f.toAlgebra
  exact (integralClosure P B).val.toRingHom

lemma square : (inclusion f).comp (scalar f)=f := rfl

lemma integral (z : Closure f) : letI := f.toAlgebra;
    IsIntegral P (inclusion f z) := by
  letI := f.toAlgebra
  exact z.property
end IntegralClosureAlongRingMap318
