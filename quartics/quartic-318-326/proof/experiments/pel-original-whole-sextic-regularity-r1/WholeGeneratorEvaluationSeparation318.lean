module
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.Localization.FractionRing
public section
noncomputable section
namespace WholeGeneratorEvaluationSeparation318
variable {F A T : Type*} [CommRing F] [CommRing A] [CommRing T]
  [Algebra F A] [Algebra F T]

/-- Actual full polynomial generation makes ALL algebra evaluations
separated by their literal generator values. -/
theorem algebra_hom_ext {ι : Type*} (a : ι → A)
    (hgen : Function.Surjective (MvPolynomial.aeval a : MvPolynomial ι F →ₐ[F] A))
    (f g : A →ₐ[F] T) (h : ∀ i, f (a i) = g (a i)) : f = g := by
  have hh : f.comp (MvPolynomial.aeval a) = g.comp (MvPolynomial.aeval a) := by
    ext i
    simpa only [AlgHom.comp_apply,MvPolynomial.aeval_X] using h i
  ext x
  obtain ⟨p,rfl⟩ := hgen x
  exact congrArg (fun k : MvPolynomial ι F →ₐ[F] T => k p) hh

/-- The SAME whole-ring generators separate embeddings of its genuine
fraction field; equality on a selected finite subset of original points
is never substituted for field generation. -/
theorem fraction_hom_ext {K L : Type*} [Field K] [Field L]
    [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [Algebra K T] [IsScalarTower F K T]
    [Algebra A L] [IsFractionRing A L] [IsScalarTower F A L]
    {ι : Type*} (a : ι → A)
    (hgen : Function.Surjective (MvPolynomial.aeval a : MvPolynomial ι F →ₐ[F] A))
    (f g : L →ₐ[K] T)
    (h : ∀ i, f (algebraMap A L (a i)) = g (algebraMap A L (a i))) : f = g := by
  have hh : (f.restrictScalars F).comp (IsScalarTower.toAlgHom F A L) =
      (g.restrictScalars F).comp (IsScalarTower.toAlgHom F A L) :=
    algebra_hom_ext a hgen _ _ h
  have hr : f.toRingHom = g.toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors A)
    exact congrArg AlgHom.toRingHom hh
  ext z
  exact congrArg (fun k : L →+* T => k z) hr
end WholeGeneratorEvaluationSeparation318
