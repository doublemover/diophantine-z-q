module
public import ContactBoundedUniversalAmbient318
public section
noncomputable section
namespace ContactBoundedUniversalFamily318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "b" => ContactBoundedHilbertParameter318.structureMap c N
local notation "π" => ContactBoundedHilbertParameter318.projection c N
local notation "ι" => ContactBoundedHilbertParameter318.familyInto c N
@[expose] def originalMap : ContactBoundedHilbertParameter318.family c N ⟶ ContactProjectiveModel318.model c :=
  Sigma.desc (fun d => ContactProjectiveUniversalGluing318.original c d.val ≫
    pullback.fst p (ContactProjectiveParameterStructure318.structureMap c d.val))
@[reassoc] lemma into_originalMap (d : Fin (N+1)) : ι d ≫ originalMap c N=
    ContactProjectiveUniversalGluing318.original c d.val ≫
      pullback.fst p (ContactProjectiveParameterStructure318.structureMap c d.val) := Sigma.ι_desc _ _
lemma compatibility : originalMap c N ≫ p=π ≫ b := by
  apply Sigma.hom_ext
  intro d
  simp only [← Category.assoc,into_originalMap,SchemeSigmaFamilyCartesian318.into_map]
  rw [Category.assoc,pullback.condition,← Category.assoc]
  rw [Category.assoc,ContactBoundedHilbertParameter318.into_structure]
  rfl
/-- Actual entire original-source closed quotient, not a support-only family. -/
@[expose] def original : ContactBoundedHilbertParameter318.family c N ⟶ pullback p b :=
  pullback.lift (originalMap c N) π (compatibility c N)
@[reassoc] lemma original_fst : original c N ≫ pullback.fst p b=originalMap c N := pullback.lift_fst _ _ _
@[reassoc] lemma original_snd : original c N ≫ pullback.snd p b=π := pullback.lift_snd _ _ _
@[reassoc] lemma into_original (d : Fin (N+1)) : ι d ≫ original c N=
    ContactProjectiveUniversalGluing318.original c d.val ≫ ContactBoundedUniversalAmbient318.into c N d := by
  apply pullback.hom_ext
  · simp only [Category.assoc,original_fst,RelativeSchemeCoefficient318.map_fst,into_originalMap]
  · simp only [Category.assoc,original_snd,RelativeSchemeCoefficient318.map_snd,← Category.assoc]
    exact SchemeSigmaFamilyCartesian318.into_map _ _ _ d
lemma cartesian (d : Fin (N+1)) : IsPullback (ι d) (ContactProjectiveUniversalGluing318.original c d.val)
    (original c N) (ContactBoundedUniversalAmbient318.into c N d) := by
  apply IsPullback.of_bot (v₂₁ := ContactProjectiveUniversalAmbient318.projection c d.val) (v₂₂ := pullback.snd p b)
  · simpa only [original_snd] using ContactBoundedHilbertParameter318.cartesian c N d
  · exact (into_original c N d).symm
  · exact ContactBoundedUniversalAmbient318.cartesian c N d
instance closed : IsClosedImmersion (original c N) := by
  apply IsZariskiLocalAtTarget.of_openCover (ContactBoundedUniversalAmbient318.cover c N)
  intro d
  rw [← (cartesian c N d).isoPullback_inv_snd]
  infer_instance
instance finite : IsFinite (original c N ≫ pullback.snd p b) := by rw [original_snd]; infer_instance
instance flat : Flat (original c N ≫ pullback.snd p b) := by rw [original_snd]; infer_instance
instance presentation : LocallyOfFinitePresentation (original c N ≫ pullback.snd p b) := by rw [original_snd]; infer_instance
end ContactBoundedUniversalFamily318
