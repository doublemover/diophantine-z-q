module
public import ContactFixedDegreeClassifierCoherence318
public section
noncomputable section
namespace RelativeSchemeCoefficient318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B S T : Scheme.{u}} (p : X ⟶ B) (b : S ⟶ B) (a : T ⟶ B)
  (f : T ⟶ S) (hf : f ≫ b=a)
/-- Coefficient change on the SAME p-first family over arbitrary schemes. -/
@[expose] def map : pullback p a ⟶ pullback p b :=
  pullback.lift (pullback.fst p a) (pullback.snd p a ≫ f)
    (by rw [Category.assoc,hf]; exact pullback.condition)
@[reassoc] lemma map_fst : map p b a f hf ≫ pullback.fst p b=pullback.fst p a :=
  pullback.lift_fst _ _ _
@[reassoc] lemma map_snd : map p b a f hf ≫ pullback.snd p b=pullback.snd p a ≫ f :=
  pullback.lift_snd _ _ _
lemma cartesian : IsPullback (map p b a f hf) (pullback.snd p a) (pullback.snd p b) f := by
  apply IsPullback.of_right (h₁₂ := pullback.fst p b) (h₂₂ := b)
  · simpa only [map_fst,hf] using IsPullback.of_hasPullback p a
  · exact map_snd p b a f hf
  · exact IsPullback.of_hasPullback p b
instance open [IsOpenImmersion f] : IsOpenImmersion (map p b a f hf) :=
  MorphismProperty.of_isPullback (cartesian p b a f hf).flip inferInstance
lemma comp {V : Scheme.{u}} (d : V ⟶ B) (g : V ⟶ T) (hg : g ≫ a=d) :
    map p a d g hg ≫ map p b a f hf=
      map p b d (g ≫ f) (by rw [Category.assoc,hf]; exact hg) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,map_fst]
  · simp only [Category.assoc,map_snd]
end RelativeSchemeCoefficient318
