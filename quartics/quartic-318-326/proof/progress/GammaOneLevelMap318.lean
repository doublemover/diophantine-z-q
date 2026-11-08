module
public import ActualJFinite318
public section
noncomputable section
namespace GammaOneLevelMap318
open GammaOneAtlas318 GammaOneFiber318 PeterssonQuotient318 QuotientJ318
open scoped MatrixGroups
set_option maxHeartbeats 0

lemma gamma1_le {N M : ℕ} (h : N∣M) : CongruenceSubgroup.Gamma1 M ≤ CongruenceSubgroup.Gamma1 N := by
  intro g hg
  obtain ⟨ha,hd,hc⟩ := (CongruenceSubgroup.Gamma1_mem M g).mp hg
  apply (CongruenceSubgroup.Gamma1_mem N g).mpr
  exact ⟨by simpa only [map_intCast,map_one] using congrArg (ZMod.castHom h (ZMod N)) ha,
    by simpa only [map_intCast,map_one] using congrArg (ZMod.castHom h (ZMod N)) hd,
    by simpa only [map_intCast,map_zero] using congrArg (ZMod.castHom h (ZMod N)) hc⟩

lemma image_le {N M : ℕ} (h : N∣M) : image M ≤ image N := by
  rintro g ⟨gamma,rfl⟩
  exact ⟨⟨gamma.val,gamma1_le h gamma.property⟩,rfl⟩

/-- The actual continuous level-forgetting map, built from literal
congruence-subgroup inclusion and actual orbit quotients. -/
@[expose] def forget {N M : ℕ} (h : N∣M) : Base (image M) → Base (image N) :=
  Quotient.lift (quotientMap N) (by
    intro a b hab
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp hab
    apply Quotient.sound
    exact MulAction.orbitRel_apply.mpr ⟨⟨g.val,image_le h g.property⟩,hg⟩)

lemma forget_projection {N M : ℕ} (h : N∣M) (tau : UpperHalfPlane) :
    forget h (quotientMap M tau)=quotientMap N tau := rfl

lemma forget_continuous {N M : ℕ} (h : N∣M) : Continuous (forget h) :=
  continuous_quot_lift _ continuous_quot_mk

lemma forget_surjective {N M : ℕ} (h : N∣M) : Function.Surjective (forget h) := by
  intro q
  obtain ⟨tau,rfl⟩ := GammaOneAtlas318.quotient_surjective N q
  exact ⟨quotientMap M tau,rfl⟩

lemma j_forget {N M : ℕ} (h : N∣M) (q : Base (image M)) : jMap N (forget h q)=jMap M q := by
  induction q using Quotient.inductionOn with
  | h tau => rfl

end GammaOneLevelMap318
