module
public import ContactProjectiveUniversalAmbient318
public section
noncomputable section
namespace RelativeSchemeIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B P A C O : Scheme.{u}} (p : X ⟶ B) (b : P ⟶ B)
  (a : A ⟶ B) (c : C ⟶ B) (o : O ⟶ B)
  (u : A ⟶ P) (v : C ⟶ P) (f : O ⟶ A) (g : O ⟶ C)
  (hu : u ≫ b=a) (hv : v ≫ b=c) (hf : f ≫ a=o) (hg : g ≫ c=o)
  (H : IsPullback f g u v)
local notation "ma" => RelativeSchemeCoefficient318.map p b a u hu
local notation "mc" => RelativeSchemeCoefficient318.map p b c v hv
local notation "mf" => RelativeSchemeCoefficient318.map p a o f hf
local notation "mg" => RelativeSchemeCoefficient318.map p c o g hg
lemma comm : mf ≫ ma=mg ≫ mc := by
  rw [RelativeSchemeCoefficient318.comp,RelativeSchemeCoefficient318.comp]
  congr 1
  exact H.w
/-- Base change of the actual parameter intersection, retaining all
four literal original p-first source products and maps. -/
lemma cartesian : IsPullback mf mg ma mc := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd p c) (v₂₂ := pullback.snd p b)
  · simpa only [RelativeSchemeCoefficient318.map_snd] using
      (RelativeSchemeCoefficient318.cartesian p a o f hf).paste_vert H
  · exact comm p b a c o u v f g hu hv hf hg H
  · exact RelativeSchemeCoefficient318.cartesian p b c v hv
end RelativeSchemeIntersection318
