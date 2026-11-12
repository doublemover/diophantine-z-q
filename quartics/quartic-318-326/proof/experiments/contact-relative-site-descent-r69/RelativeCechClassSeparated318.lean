module
public import RigidifiedCanonicalIsoDescent318
public section
noncomputable section
namespace RelativeCechClassSeparated318
open AlgebraicGeometry CategoryTheory LineSheafClass318 RelativeRigidifiedLine318
open RigidifiedRelativeClass318 RelativeLineClassQuotient318 RigidifiedCechNerve318
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X X' S S' : Scheme.{u}} (f : X' ⟶ X) (g : S' ⟶ S)
  (e : S ⟶ X) (e' : S' ⟶ X') (pointed : e' ≫ f = g ≫ e)
  (p : X ⟶ S) (p' : X' ⟶ S') (square : f ≫ p = p' ≫ g)
  (hs : e ≫ p = 𝟙 S) (hs' : e' ≫ p' = 𝟙 S')
  [IsAffineHom f] [Flat f] [Surjective f]

include hs hs' in
/-- Original relative classes are separated by this cover when evaluation
is bijective on the actual local section and injective on its actual double.
The proof descends an actual original isomorphism, not just a class label. -/
lemma map_injective (hl : Function.Bijective e'.appTop)
    (hd : Function.Injective (doubleSection f g e e' pointed).appTop) :
    Function.Injective (RelativeLineClassQuotient318.map p p' f g square) := by
  intro c d h
  let L := RigidifiedClassQuotient318.representative e p hs c
  let M := RigidifiedClassQuotient318.representative e p hs d
  have hc := RigidifiedClassQuotient318.representative_class e p hs c
  have hd' := RigidifiedClassQuotient318.representative_class e p hs d
  have heq : relativeClass p' e' (RigidifiedCanonicalOverlap318.pulled f g e e' pointed L) =
      relativeClass p' e' (RigidifiedCanonicalOverlap318.pulled f g e e' pointed M) := by
    rw [RigidifiedPointedPullback318.relativeClass_line e e' f g pointed p p' square,
      RigidifiedPointedPullback318.relativeClass_line e e' f g pointed p p' square,hc,hd']
    exact h
  obtain ⟨a⟩ := (relative_eq_iff_compatible p' e' hs' hl _ _).mp heq
  have hclass := LineSheafClass318.classOf_eq
    (RigidifiedCanonicalIsoDescent318.iso f g e e' pointed a hd)
  have hrel := congrArg (classMap p) hclass
  change relativeClass p e L = relativeClass p e M at hrel
  exact hc.symm.trans (hrel.trans hd')

include hs hs' in
/-- Existence and uniqueness for the unchanged relative-class Čech
matching problem. Actual local, double and triple evaluation hypotheses
are explicit; no general representability or sheaf theorem is inferred. -/
theorem matching_unique (hl : Function.Bijective e'.appTop)
    (hd : Function.Bijective (doubleSection f g e e' pointed).appTop)
    (ht : Function.Injective (tripleSection f g e e' pointed).appTop)
    (c : RelativeClass p')
    (hm : RelativeCechClassEffectivity318.firstMap f g p p' square c =
      RelativeCechClassEffectivity318.secondMap f g p p' square c) :
    ∃! d : RelativeClass p, RelativeLineClassQuotient318.map p p' f g square d = c := by
  obtain ⟨d,hdc⟩ := RelativeCechClassEffectivity318.matching_effective
    f g e e' pointed p p' square hs' c hm hd hl.injective ht
  exact ⟨d,hdc,fun d' hd' => map_injective f g e e' pointed p p' square hs hs'
    hl hd.injective (hd'.trans hdc.symm)⟩
end RelativeCechClassSeparated318
