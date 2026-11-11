module
public import PELActualLevelThreeQuotient318
public import PELOriginalPeriodLattice318
public section
noncomputable section
namespace PELOriginalThirdPeriods318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
set_option maxHeartbeats 1200000
variable (τ : ℂ)
abbrev Torus := PeriodQuotient representation order τ
@[expose] def quotientMap : ComplexVectors →+ Torus τ :=
  QuotientAddGroup.mk' (periodSubgroup representation order τ)
@[expose] def originalPeriods : order →+ ComplexVectors :=
  (periodHom representation τ).comp order.subtype.toAddMonoidHom

/-- Injectivity uses the specified faithful real splitting and the actual
upper-half-plane period map, not an unrelated lattice of equal rank. -/
theorem originalPeriods_injective (hτ : 0<τ.im) : Function.Injective (originalPeriods τ) := by
  intro a b h
  apply Subtype.ext
  apply representation_injective
  apply (periodEquiv τ hτ).injective
  exact h

/-- Exact membership in the entire original period subgroup. -/
theorem quotient_zero_iff (z : ComplexVectors) :
    quotientMap τ z=0 ↔ ∃ a : order, originalPeriods τ a=z := by
  change QuotientAddGroup.mk' (periodSubgroup representation order τ) z=0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨a,ha,he⟩
    exact ⟨⟨a,ha⟩,he⟩
  · rintro ⟨a,ha⟩
    exact ⟨(a:PELQuaternionAlgebra318.B),a.property,ha⟩

/-- Division occurs in the actual period vector space before the quotient. -/
@[expose] def thirdVector : order →+ ComplexVectors where
  toFun a := (1/3:ℝ) • originalPeriods τ a
  map_zero' := by simp
  map_add' a b := by simp [smul_add]

@[expose] def thirdPeriod : order →+ Torus τ := (quotientMap τ).comp (thirdVector τ)

theorem three_third_vector (z : ComplexVectors) :
    (3:ℤ) • ((1/3:ℝ) • z)=z := by
  rw [← Int.cast_smul_eq_zsmul ℝ,smul_smul]
  norm_num

theorem third_three_vector (z : ComplexVectors) :
    (1/3:ℝ) • ((3:ℤ) • z)=z := by
  rw [← Int.cast_smul_eq_zsmul ℝ,smul_smul]
  norm_num

theorem three_third (a : order) : (3:ℤ) • thirdVector τ a=originalPeriods τ a :=
  three_third_vector _

theorem third_killed (a : order) : (3:ℤ) • thirdPeriod τ a=0 := by
  change (3:ℤ) • quotientMap τ (thirdVector τ a)=0
  rw [← map_zsmul,three_third]
  exact (quotient_zero_iff τ _).mpr ⟨a,rfl⟩

/-- Exact kernel3O of the actual third-period map. -/
theorem third_kernel (hτ : 0<τ.im) (a : order) :
    thirdPeriod τ a=0 ↔ ∃ b : order, a=(3:ℤ) • b := by
  constructor
  · intro h
    obtain ⟨b,hb⟩ := (quotient_zero_iff τ (thirdVector τ a)).mp h
    refine ⟨b,originalPeriods_injective τ hτ ?_⟩
    rw [map_zsmul]
    calc
      originalPeriods τ a = (3:ℤ) • thirdVector τ a := (three_third τ a).symm
      _ = (3:ℤ) • originalPeriods τ b := congrArg ((3:ℤ) • ·) hb.symm
  · rintro ⟨b,rfl⟩
    rw [map_zsmul]
    exact third_killed τ b

/-- Every actual3-torsion point has an original-order third-period lift.
This is not just the construction of81 selected points. -/
theorem third_surjective (x : Torus τ) (hx : (3:ℤ) • x=0) :
    ∃ a : order, thirdPeriod τ a=x := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective (periodSubgroup representation order τ) x
  have hz : quotientMap τ ((3:ℤ) • z)=0 := by rw [map_zsmul]; exact hx
  obtain ⟨a,ha⟩ := (quotient_zero_iff τ _).mp hz
  refine ⟨a,?_⟩
  change quotientMap τ ((1/3:ℝ) • originalPeriods τ a)=quotientMap τ z
  rw [ha,third_three_vector]
end PELOriginalThirdPeriods318
