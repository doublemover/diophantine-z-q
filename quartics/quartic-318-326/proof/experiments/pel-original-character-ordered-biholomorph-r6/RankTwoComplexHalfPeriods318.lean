module
public import ComplexAffineFreeTranslation318
public section
noncomputable section
namespace RankTwoComplexHalfPeriods318
open ComplexAffineFreeTranslation318
set_option maxHeartbeats 2400000
abbrev Coordinates := Fin 2→ℤ
variable (L : AddSubgroup ℂ) (basis : Coordinates ≃+ L)
@[expose] def periods : Coordinates →+ ℂ := L.subtype.comp basis.toAddMonoidHom
@[expose] def halfVector : Coordinates →+ ℂ where
  toFun a := periods L basis a/2
  map_zero' := by simp
  map_add' a b := by simp [add_div]
@[expose] def halfPeriod : Coordinates →+ Torus L :=
  (projection L).comp (halfVector L basis)

lemma periods_injective : Function.Injective (periods L basis) := by
  intro a b he
  exact basis.injective (Subtype.ext he)
lemma projection_zero_iff (z : ℂ) : projection L z=0 ↔ ∃ a,periods L basis a=z := by
  rw [projection,QuotientAddGroup.eq_zero_iff]
  constructor
  · intro hz
    obtain ⟨a,ha⟩ := basis.surjective ⟨z,hz⟩
    exact ⟨a,congrArg Subtype.val ha⟩
  · rintro ⟨a,rfl⟩
    exact (basis a).property
lemma twice_half (a : Coordinates) : (2:ℤ) • halfVector L basis a=periods L basis a := by
  change (2:ℤ) • (periods L basis a/2)=_
  simp only [two_zsmul]
  ring
lemma half_twice (z : ℂ) : ((2:ℤ) • z)/2=z := by
  simp only [two_zsmul]
  ring
lemma half_killed (a : Coordinates) : (2:ℤ) • halfPeriod L basis a=0 := by
  change (2:ℤ) • projection L (halfVector L basis a)=0
  rw [←map_zsmul,twice_half]
  exact (projection_zero_iff L basis _).mpr ⟨a,rfl⟩

/-- Exact kernel2Z² in the specified actual rank-two period basis. -/
theorem half_kernel (a : Coordinates) :
    halfPeriod L basis a=0 ↔ ∃ b,a=(2:ℤ) • b := by
  constructor
  · intro ha
    obtain ⟨b,hb⟩ := (projection_zero_iff L basis _).mp ha
    refine ⟨b,periods_injective L basis ?_⟩
    rw [map_zsmul]
    calc
      periods L basis a = (2:ℤ) • halfVector L basis a := (twice_half L basis a).symm
      _ = (2:ℤ) • periods L basis b := congrArg ((2:ℤ) • ·) hb.symm
  · rintro ⟨b,rfl⟩
    rw [map_zsmul]
    exact half_killed L basis b

/-- Every two-torsion point of the whole complex quotient has a half-period
from the SAME rank-two lattice, not merely four selected examples. -/
theorem half_surjective (p : Torus L) (hp : (2:ℤ) • p=0) :
    ∃ a,halfPeriod L basis a=p := by
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective L p
  have hz : projection L ((2:ℤ) • z)=0 := by rw [map_zsmul]; exact hp
  obtain ⟨a,ha⟩ := (projection_zero_iff L basis _).mp hz
  refine ⟨a,?_⟩
  change projection L (periods L basis a/2)=projection L z
  rw [ha,half_twice]
end RankTwoComplexHalfPeriods318
