module
public import ActualQuadraticFieldDiscriminant318
public import CMFieldContactSupport318
public section
namespace ActualCMQuadraticDiscriminantBound318
open ActualFieldRamificationSupport318 ContactRadical318

/-- Field-level CM discriminant bound for any actual quadratic subfield of a
controlled-ramification field. Its fundamental signed discriminant is proved,
not a supplied numerical certificate. Construction and local ramification
of the controlled field remain separate PEL arithmetic obligations. -/
theorem bound (u v : ℤ) (K F : Type*) [Field K] [NumberField K]
    [Field F] [NumberField F] [Algebra K F] (hd : Module.finrank ℚ K=2)
    (hr : UnramifiedOutside F (badPrimes ∪ contactPrimes u v)) :
    (NumberField.discr K).natAbs ≤ 4*(badProduct*radical u v) :=
  CMFieldContactSupport318.quadratic_bound u v K F
    (ActualQuadraticFieldDiscriminant318.fundamental K hd) hr
end ActualCMQuadraticDiscriminantBound318
