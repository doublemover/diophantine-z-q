module
public import RelativeSchemeCoefficient318
public section
noncomputable section
namespace RelativeSchemeOpenChart318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B S U : Scheme.{u}} (p : X ⟶ B) (b : S ⟶ B)
  (j : U ⟶ X) (a : U ⟶ B) (hj : j ≫ p=a)
/-- The literal source open chart over an arbitrary coefficient scheme,
with its base-first product identified with the p-first original family. -/
@[expose] def comparison : pullback j (pullback.fst p b) ≅ pullback b a :=
  pullbackRightPullbackFstIso p b j ≪≫ pullback.congrHom hj rfl ≪≫ pullbackSymmetry a b
@[expose] def into : pullback b a ⟶ pullback p b :=
  (comparison p b j a hj).inv ≫ pullback.snd j (pullback.fst p b)
instance open [IsOpenImmersion j] : IsOpenImmersion (into p b j a hj) := by
  unfold into
  infer_instance
@[reassoc] lemma into_base : into p b j a hj ≫ pullback.snd p b=pullback.fst b a := by
  simp only [into,comparison,Iso.trans_inv,Category.assoc,pullbackRightPullbackFstIso_inv_snd_snd,
    pullback.congrHom_inv,pullback.map,pullback.lift_snd,Category.comp_id,pullbackSymmetry_inv_comp_snd]
@[reassoc] lemma into_original : into p b j a hj ≫ pullback.fst p b=pullback.snd b a ≫ j := by
  simp only [into,comparison,Iso.trans_inv,Category.assoc,pullbackRightPullbackFstIso_inv_snd_fst,
    pullback.congrHom_inv,pullback.map,pullback.lift_fst_assoc,Category.id_comp,Category.comp_id,
    pullbackSymmetry_inv_comp_fst_assoc]
end RelativeSchemeOpenChart318
