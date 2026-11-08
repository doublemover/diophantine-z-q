module
public import CharacterBooleanAffine318
public import CharacterSignGlobal318
public section
noncomputable section
namespace CharacterBooleanGlobal318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318 CompletedCharacterGlobal318
open CharacterSignGlobal318 CharacterBooleanAffine318
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
lemma open_positive (i:Fin 4) (b:Fin 4→Bool) (h:epsilon i b=1):
    ContactGlobalSigns318.openMap units b≫affineMap i=affineMap i:=by
  unfold ContactGlobalSigns318.openMap affineMap
  rw [←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (positive_affine i b h))
lemma open_negative (i:Fin 4) (b:Fin 4→Bool) (h:epsilon i b=-1):
    ContactGlobalSigns318.openMap units b≫affineMap i=
      affineMap i≫GluedNegation318.finiteNeg (publishedA i) (publishedB i):=by
  unfold ContactGlobalSigns318.openMap affineMap GluedNegation318.finiteNeg
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (congrArg AlgHom.toRingHom (negative_affine i b h))
/-- Every positive character sign fixes the entire actual quotient morphism. -/
theorem positive (i:Fin 4) (b:Fin 4→Bool) (h:epsilon i b=1):
    ContactGlobalSigns318.map units b≫completedMap i=completedMap i:=by
  apply source_ext i _ _ (signed_over_Q i b)
  rw [←Category.assoc,ContactGlobalSigns318.on_open,Category.assoc,on_open,
    ←Category.assoc,open_positive i b h]
/-- Every negative character sign induces the actual whole elliptic inverse. -/
theorem negative (i:Fin 4) (b:Fin 4→Bool) (h:epsilon i b=-1):
    ContactGlobalSigns318.map units b≫completedMap i=
      completedMap i≫GluedNegation318.negation (publishedA i) (publishedB i):=by
  apply source_ext i
  · simpa only [Category.assoc,GluedNegation318.negation_over_base] using signed_over_Q i b
  · rw [←Category.assoc,ContactGlobalSigns318.on_open,Category.assoc,on_open,
      ←Category.assoc,open_negative i b h,Category.assoc]
    rw [←Category.assoc (ContactProjectiveModel318.sourceOpen units) (completedMap i),on_open]
    simp only [Category.assoc,GluedNegation318.finiteChart_negation]
/-- The precise stabilizer is proved in both directions, not only as a
subgroup known to act trivially. -/
theorem fixes_iff (i:Fin 4) (b:Fin 4→Bool):
    ContactGlobalSigns318.map units b≫completedMap i=completedMap i↔epsilon i b=1:=by
  refine ⟨?_,positive i b⟩
  intro h
  have ho:=congrArg (fun f=>ContactProjectiveModel318.sourceOpen units≫f) h
  rw [←Category.assoc,ContactGlobalSigns318.on_open,Category.assoc,on_open,
    ←Category.assoc] at ho
  have ha:ContactGlobalSigns318.openMap units b≫affineMap i=affineMap i:=
    (cancel_mono (WeierstrassGluing318.finiteChart (publishedA i) (publishedB i))).mp ho
  unfold ContactGlobalSigns318.openMap affineMap at ha
  rw [←Spec.map_comp] at ha
  have hr:=Spec.map_injective ha
  have hy:=congrArg (fun f=>SourceOpenFractionField318.openEmbedding units
    (f.hom (ShortAffineJacobian318.y (publishedA i) (publishedB i)))) hr
  change SourceOpenFractionField318.openEmbedding units
    (ContactGlobalSigns318.openEquiv units b (CharacterSignAffine318.openPublished i _))=
      SourceOpenFractionField318.openEmbedding units (CharacterSignAffine318.openPublished i _) at hy
  rw [SourceSignFieldComparison318.open_embedding,CharacterSignAffine318.openPublished_embedding] at hy
  exact (sigma_y_fixed_iff i b).mp hy
/-- Literal target action for all sixteen original signs. -/
@[expose] def targetMap (i:Fin 4) (b:Fin 4→Bool):Target i⟶Target i:=
  if epsilon i b=1 then 𝟙 _ else GluedNegation318.negation (publishedA i) (publishedB i)
theorem equivariant (i:Fin 4) (b:Fin 4→Bool):
    ContactGlobalSigns318.map units b≫completedMap i=completedMap i≫targetMap i b:=by
  unfold targetMap
  by_cases h:epsilon i b=1
  · simpa only [if_pos h,Category.comp_id] using positive i b h
  · simpa only [if_neg h] using negative i b ((epsilon_values i b).resolve_left h)
end CharacterBooleanGlobal318
