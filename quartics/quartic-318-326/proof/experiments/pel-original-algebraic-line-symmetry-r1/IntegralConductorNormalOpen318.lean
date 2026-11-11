module
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.Integral
public section
noncomputable section
namespace IntegralConductorNormalOpen318
open scoped nonZeroDivisors
variable (A : Type*) [CommRing A] [IsDomain A]

/-- A conductor for ALL integral fraction-field elements makes its
principal localization normal. Clearing the integral equation denominator
is essential: an element integral over A[1/d] need not be integral over A. -/
theorem integrallyClosed (d : A) (hd : d ≠ 0)
    (hc : ∀ y : FractionRing A, IsIntegral A y →
      ∃ a : A, algebraMap A (FractionRing A) d * y = algebraMap A (FractionRing A) a) :
    IsIntegrallyClosed (Localization.Away d) := by
  let M := Submonoid.powers d
  let B := Localization.Away d
  let K := FractionRing A
  have hM : M ≤ A⁰ := by
    rintro m ⟨n,rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd)
  let g : B →+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
  letI : Algebra B K := g.toAlgebra
  letI : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp,RingHomCompTriple.comp_eq])
  letI : IsFractionRing B K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M B K
  apply (isIntegrallyClosed_iff K).mpr
  intro y hy
  obtain ⟨⟨m,hm⟩,hym⟩ := hy.exists_multiple_integral_of_isLocalization M y
  obtain ⟨a,ha⟩ := hc _ hym
  have hdm : d*m ∈ M := mul_mem (Submonoid.mem_powers d) hm
  refine ⟨IsLocalization.mk' B a ⟨d*m,hdm⟩,
    (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
  rw [RingHom.comp_id]
  change algebraMap A K a = algebraMap A K (d*m) * y
  rw [map_mul]
  have he : algebraMap A K d * (algebraMap A K m * y) = algebraMap A K a := by
    simpa only [Submonoid.smul_def,Submonoid.mk_smul,Algebra.smul_def] using ha
  exact he.symm.trans (mul_assoc _ _ _).symm
end IntegralConductorNormalOpen318
