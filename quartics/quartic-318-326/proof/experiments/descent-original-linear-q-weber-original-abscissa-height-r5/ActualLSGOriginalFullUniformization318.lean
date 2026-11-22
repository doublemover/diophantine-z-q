module
public import ActualLSGOriginalPositiveIScale318
public import ActualLSGWeierstrassSurjectivity318
public import ActualGaussianWeberOriginalUniformization318
import all ActualLSGOriginalPositiveIScale318
public section
noncomputable section

namespace ActualLSGOriginalFullUniformization318

open Complex
open LSG.Weierstrass LSG.LemniscateIndep
open ActualLSGUnitSquarePeriod318 ActualLSGOriginalPositiveIScale318
open ActualLSGWeierstrassSurjectivity318
open ActualGaussianWeberHenselianPointMap318
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberQuarterTurn318
open ActualGaussianComplexTorusKernel318 ActualGaussianWeberComplexUniformizationFibres318

attribute [local instance] Classical.decEq

private theorem surj_comp {A B : Type*} [AddMonoid A] [AddMonoid B]
    (e : A ≃+ B) (g : ℂ →+ A) (hg : Function.Surjective g) :
    Function.Surjective (e.toAddMonoidHom.comp g) := e.surjective.comp hg

private theorem ker_comp {A B : Type*} [AddGroup A] [AddGroup B]
    (e : A ≃+ B) (g : ℂ →+ A) :
    (e.toAddMonoidHom.comp g).ker=g.ker := by
  ext x
  change e (g x)=0 ↔ g x=0
  rw [←e.map_zero,e.injective.eq_iff]

/-- Surjectivity of the already fixed actual scale map, inherited
from the official same-period LSG analytic result. -/
theorem exp_surjective : Function.Surjective expOriginal := by
  unfold expOriginal
  apply surj_comp
  intro P
  obtain ⟨z,h⟩ := expE_surjective L P
  exact ⟨z,by simpa only [expHom_apply] using h⟩

/-- The normalized map uses the same literal positive Gaussian lattice. -/
theorem exp_kernel : expOriginal.ker=lattice := by
  unfold expOriginal
  rw [ker_comp,expHom_kernel]
  ext z
  change z∈L.lattice ↔ z∈lattice
  rw [mem_lattice_sq period_one period_i]
  constructor
  · rintro ⟨a,b,h⟩
    refine ⟨literal a b,?_⟩
    change (((⟨a,b⟩ : GaussianInt) : ℂ)) = z
    simpa only [GaussianInt.toComplex_def',Complex.ofReal_one,mul_one] using h
  · rintro ⟨u,h⟩
    obtain ⟨a,b⟩ := u
    refine ⟨a,b,?_⟩
    change (((⟨a,b⟩ : GaussianInt) : ℂ)) = z at h
    simpa only [GaussianInt.toComplex_def',Complex.ofReal_one,mul_one] using h

/-- No analytic structure is supplied as an input: this constructs
the original U from the actual normalized stock exponential,
its exact unit-square kernel, and its positive-i rotation. -/
def uniformization : OriginalUniformization := by
  let E := QuotientAddGroup.liftEquiv lattice exp_surjective exp_kernel.symm
  have hE (z : ℂ) : E (V z)=expOriginal z :=
    QuotientAddGroup.liftEquiv_coe lattice exp_surjective exp_kernel.symm z
  refine ⟨E,?_⟩
  intro P
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective lattice P
  rw [scalar_on]
  have hI : iota gaussianI=Complex.I := by
    change (((⟨0,1⟩ : GaussianInt) : ℂ)) = Complex.I
    rw [GaussianInt.toComplex_def'] <;> norm_num
  rw [hI]
  change E (V (Complex.I*z))=turn _ Complex.I Complex.I_sq (E (V z))
  calc
    _ = expOriginal (Complex.I*z) := hE _
    _ = turn _ Complex.I Complex.I_sq (expOriginal z) := exp_I z
    _ = _ := congrArg (turn _ Complex.I Complex.I_sq) (hE _).symm

theorem uniformization_on (z : ℂ) : uniformization.point (V z)=expOriginal z := by
  unfold uniformization
  exact QuotientAddGroup.liftEquiv_coe lattice exp_surjective exp_kernel.symm z

end ActualLSGOriginalFullUniformization318
