module
public import RankTwoComplexTwoTorsion318
public section
noncomputable section
namespace PELOriginalDeckTwoTorsion318
open PELOriginalInvolutionTower318 PELOriginalResidualDeckAction318
open PELOriginalResidualDeckFibers318 ComplexAffineFreeTranslation318
set_option maxHeartbeats 2400000
variable (i : Fin 4) (L : AddSubgroup ℂ) (u : InvolutionBase i ≃ Torus L)

/-- This is the genuine remaining analytic producer: a uniformization of
THIS involution curve and affine lifts of THESE original deck maps. It is
not a supplied torsion action, isogeny, same-j statement or model identity. -/
@[expose] def AffineLifts : Prop :=
  ∀ g : Deck i,∃ a b : ℂ,∀ z : ℂ,
    u (g • u.symm (projection L z))=projection L (a*z+b)

@[expose] def displacement (g : Deck i) : Torus L := u (g • u.symm 0)

/-- The original deck transformations become translations as a consequence
of freeness and an affine lift, not as part of the uniformization input. -/
theorem deck_translation (hlift : AffineLifts i L u) (g : Deck i)
    (p : InvolutionBase i) : u (g • p)=u p+displacement i L u g := by
  by_cases hg : g=1
  · subst g
    simp [displacement]
  · obtain ⟨a,b,hab⟩ := hlift g
    have hfree : ∀ z : Torus L,u (g • u.symm z)≠z := by
      intro z hz
      have he : g • u.symm z=u.symm z := u.injective (hz.trans (u.apply_symm_apply z).symm)
      exact hg ((deck_fixed_iff i g (u.symm z)).mp he)
    have ht := (free_is_translation L (fun z => u (g • u.symm z)) a b hab hfree).2
    have hzero : displacement i L u g=projection L b := by
      simpa only [displacement,zero_add] using ht 0
    rw [hzero]
    simpa only [u.symm_apply_apply] using ht (u p)

theorem displacement_injective : Function.Injective (displacement i L u) := by
  intro g h he
  apply (orbitFiber_bijective i (u.symm 0)).1
  exact Subtype.ext (u.injective he)

/-- Exponent two is proved for the old residual group, so its actual
translation displacement lies in the full period two-torsion subgroup. -/
theorem displacement_two (hlift : AffineLifts i L u) (g : Deck i) :
    (2:ℤ) • displacement i L u g=0 := by
  have he : u (g • (g • u.symm 0))=0 := by
    rw [←mul_smul,deck_square,one_smul,u.apply_symm_apply]
  rw [deck_translation i L u hlift g,deck_translation i L u hlift g,
    u.apply_symm_apply,zero_add] at he
  simpa only [two_zsmul] using he

@[expose] def torsionMap (hlift : AffineLifts i L u) : Deck i→RankTwoComplexTwoTorsion318.torsion L :=
  fun g => ⟨displacement i L u g,displacement_two i L u hlift g⟩

/-- All, not just some, two-torsion translations occur: injectivity follows
from the original free action; both cardinalities4 are constructed. -/
theorem torsionMap_bijective (basis : RankTwoComplexHalfPeriods318.Coordinates ≃+ L)
    (hlift : AffineLifts i L u) : Function.Bijective (torsionMap i L u hlift) := by
  letI : Finite (RankTwoComplexTwoTorsion318.torsion L) :=
    RankTwoComplexTwoTorsion318.torsion_finite L basis
  letI : Fintype (Deck i) := Fintype.ofFinite _
  letI : Fintype (RankTwoComplexTwoTorsion318.torsion L) := Fintype.ofFinite _
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_,?_⟩
  · intro g h he
    exact displacement_injective i L u (congrArg Subtype.val he)
  · rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,
      deck_card,RankTwoComplexTwoTorsion318.torsion_card L basis]
end PELOriginalDeckTwoTorsion318
