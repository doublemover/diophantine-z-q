module
public import SelectedProjectiveJScalarPullback318
public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open SelectedProjectiveJScalarPullback318

namespace SelectedCanonicalCompactScalar318
universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
local notation "b" => Spec.algebraMap R S
local notation "q" => SelectedProjectiveJScalar318.scalarMap (algebraMap R S)

/-- The literal constant extension of the same original source
over its actual j-line structure, not an independently supplied
scheme equipped with a pullback certificate. -/
abbrev source {X : Scheme.{u}} (j : X ⟶ ProjectiveJLine318.scheme R) : Scheme.{u} :=
  pullback (j ≫ ProjectiveJLine318.structureMap R) b

abbrev sourceProjection {X : Scheme.{u}} (j : X ⟶ ProjectiveJLine318.scheme R) :
    source R S j ⟶ X :=
  pullback.fst (j ≫ ProjectiveJLine318.structureMap R) b

abbrev scalarProjection {X : Scheme.{u}} (j : X ⟶ ProjectiveJLine318.scheme R) :
    source R S j ⟶ Spec (CommRingCat.of S) :=
  pullback.snd (j ≫ ProjectiveJLine318.structureMap R) b

/-- Same j-map on the specific constant extension, constructed
by the actual projective universal property. -/
@[expose] def modularMap {X : Scheme.{u}} (j : X ⟶ ProjectiveJLine318.scheme R) :
    source R S j ⟶ ProjectiveJLine318.scheme S :=
  changedJ R S j (sourceProjection R S j) (scalarProjection R S j)
    (IsPullback.of_hasPullback (j ≫ ProjectiveJLine318.structureMap R) b)

@[reassoc] theorem modularMap_q {X : Scheme.{u}} (j : X ⟶ ProjectiveJLine318.scheme R) :
    modularMap R S j ≫ q = sourceProjection R S j ≫ j :=
  changedJ_q R S j _ _ (IsPullback.of_hasPullback (j ≫ ProjectiveJLine318.structureMap R) b)

@[reassoc] theorem modularMap_base {X : Scheme.{u}} (j : X ⟶ ProjectiveJLine318.scheme R) :
    modularMap R S j ≫ ProjectiveJLine318.structureMap S = scalarProjection R S j :=
  changedJ_base R S j _ _ (IsPullback.of_hasPullback (j ≫ ProjectiveJLine318.structureMap R) b)

theorem modular_pullback {X : Scheme.{u}} (j : X ⟶ ProjectiveJLine318.scheme R) :
    IsPullback (sourceProjection R S j) (modularMap R S j) j q :=
  changedJ_pullback R S j _ _ (IsPullback.of_hasPullback (j ≫ ProjectiveJLine318.structureMap R) b)

section OverJ
variable {X Y : Scheme.{u}} (jX : X ⟶ ProjectiveJLine318.scheme R)
  (jY : Y ⟶ ProjectiveJLine318.scheme R) (e : X ≅ Y) (he : e.hom ≫ jY = jX)

/-- Extend an actual over-j comparison of the entire original models.
It is not an isomorphism with a component picked after base change. -/
@[expose] def sourceIso : source R S jX ≅ source R S jY := by
  let f := pullback.map (jX ≫ ProjectiveJLine318.structureMap R) b
    (jY ≫ ProjectiveJLine318.structureMap R) b e.hom (𝟙 _) (𝟙 _)
    (by rw [Category.comp_id, ← Category.assoc, he])
    (by rw [Category.comp_id,Category.id_comp])
  letI : IsIso f := by dsimp only [f]; infer_instance
  exact asIso f

@[reassoc] theorem sourceIso_original :
    (sourceIso R S jX jY e he).hom ≫ sourceProjection R S jY =
      sourceProjection R S jX ≫ e.hom := by
  simp [sourceIso,sourceProjection]

@[reassoc] theorem sourceIso_scalar :
    (sourceIso R S jX jY e he).hom ≫ scalarProjection R S jY = scalarProjection R S jX := by
  simp [sourceIso,scalarProjection]

/-- The actual scalar comparison keeps the modular map itself;
equality is forced by the two original projections of the
genuine projective pullback, not an assumed new compatibility. -/
@[reassoc] theorem sourceIso_over :
    (sourceIso R S jX jY e he).hom ≫ modularMap R S jY = modularMap R S jX := by
  apply (projective_pullback R S).hom_ext
  · calc
      _ = (sourceIso R S jX jY e he).hom ≫ sourceProjection R S jY ≫ jY := by
        simp only [Category.assoc,modularMap_q]
      _ = sourceProjection R S jX ≫ e.hom ≫ jY := by
        rw [← Category.assoc, sourceIso_original, Category.assoc]
      _ = _ := by rw [he,modularMap_q]
  · simp only [Category.assoc,modularMap_base,sourceIso_scalar]

end OverJ
end SelectedCanonicalCompactScalar318

#print axioms SelectedCanonicalCompactScalar318.modular_pullback
#print axioms SelectedCanonicalCompactScalar318.sourceIso_over
