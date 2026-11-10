module
public import PELOriginalDeckTwoTorsion318
public section
noncomputable section
namespace PELOriginalDoublingFactor318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalResidualDeckAction318 PELOriginalDeckTwoTorsion318
open PELOriginalCharacterQuotient318 ComplexAffineFreeTranslation318
set_option maxHeartbeats 2600000
variable (i : Fin 4) (L : AddSubgroup ℂ) (u : InvolutionBase i ≃ Torus L)
variable (basis : RankTwoComplexHalfPeriods318.Coordinates ≃+ L)
variable (hlift : AffineLifts i L u)

include basis hlift in
/-- Exact equality of the original residual fibers and the fibers of
multiplication-by-two on the SAME period quotient. -/
theorem doubling_fiber (p q : InvolutionBase i) :
    toCharacterBase i p=toCharacterBase i q ↔ (2:ℤ) • u p=(2:ℤ) • u q := by
  constructor
  · intro hpq
    obtain ⟨g,rfl⟩ := (fiber_iff_orbit i p q).mp hpq
    rw [deck_translation i L u hlift g,smul_add,displacement_two i L u hlift g,add_zero]
  · intro hpq
    have ht : (2:ℤ) • (u p-u q)=0 := by rw [smul_sub,hpq,sub_self]
    obtain ⟨g,hg⟩ := (torsionMap_bijective i L u basis hlift).2 ⟨u p-u q,ht⟩
    have hv : displacement i L u g=u p-u q := congrArg Subtype.val hg
    have hp : g • q=p := by
      apply u.injective
      rw [deck_translation i L u hlift g,hv]
      abel
    exact (fiber_iff_orbit i p q).mpr ⟨g,hp⟩

/-- Descent from the literal original character orbit quotient. The map
is not chosen from cardinality or an abstract isogeny existence theorem. -/
@[expose] def doublingFactor : CharacterBase i→Torus L :=
  Quotient.lift (fun x => (2:ℤ) • u (toInvolution i x)) (by
    intro x y h
    apply (doubling_fiber i L u basis hlift (toInvolution i x) (toInvolution i y)).mp
    exact Quotient.sound h)

theorem doublingFactor_square (p : InvolutionBase i) :
    doublingFactor i L u basis hlift (toCharacterBase i p)=(2:ℤ) • u p := by
  obtain ⟨x,rfl⟩ := toInvolution_surjective i p
  rfl

lemma torus_doubling_surjective : Function.Surjective (fun p : Torus L => (2:ℤ) • p) := by
  intro p
  obtain ⟨z,rfl⟩ := QuotientAddGroup.mk'_surjective L p
  refine ⟨projection L (z/2),?_⟩
  rw [←map_zsmul]
  congr 1
  simp only [two_zsmul]
  ring

theorem doublingFactor_bijective : Function.Bijective (doublingFactor i L u basis hlift) := by
  constructor
  · intro x y he
    obtain ⟨p,rfl⟩ := toCharacterBase_surjective i x
    obtain ⟨q,rfl⟩ := toCharacterBase_surjective i y
    rw [doublingFactor_square,doublingFactor_square] at he
    exact (doubling_fiber i L u basis hlift p q).mpr he
  · intro x
    obtain ⟨z,hz⟩ := torus_doubling_surjective L x
    refine ⟨toCharacterBase i (u.symm z),?_⟩
    rw [doublingFactor_square,u.apply_symm_apply]
    exact hz

/-- Under the explicit uniformization and affine-lift producers, the
original character curve has a concrete bijection to the SAME torus and
the original cover is exactly[2] in these coordinates. Holomorphy of the
uniformization and this comparison must still be supplied for equal-j. -/
@[expose] def characterEquiv : CharacterBase i ≃ Torus L :=
  Equiv.ofBijective (doublingFactor i L u basis hlift)
    (doublingFactor_bijective i L u basis hlift)
end PELOriginalDoublingFactor318
