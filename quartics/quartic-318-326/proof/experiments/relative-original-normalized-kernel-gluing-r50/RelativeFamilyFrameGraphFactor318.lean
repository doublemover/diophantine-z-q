module
public import RelativeFamilyFrameGraphNaturality318
public section
noncomputable section
namespace RelativeFamilyFrameGraphFactor318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open RelativeFamilyFrameGraph318 OriginalFramePathTransport318
universe u
variable {X B : Scheme.{u}} (p : X ⟶ B) (L : Line X)
  (F : RelativeFamilyFrameRule318.Rule p L)
  (S T : CommRingCat.{u}) (b : Spec S ⟶ B) (t : Spec T ⟶ pullback p b)
abbrev original := t ≫ pullback.fst p b
abbrev coefficient := t ≫ pullback.snd p b
lemma over : coefficient p S T b t ≫ b=original p S T b t ≫ p := by
  simp only [coefficient,original,Category.assoc,pullback.condition]
abbrev changeFamily := RelativeSchemeCoefficient318.map p b (original p S T b t ≫ p)
  (coefficient p S T b t) (over p S T b t)
lemma factor : graph p T (original p S T b t) ≫ changeFamily p S T b t=t := by
  apply pullback.hom_ext
  · rw [Category.assoc,RelativeSchemeCoefficient318.map_fst,graph_fst]
  · rw [Category.assoc,RelativeSchemeCoefficient318.map_snd,←Category.assoc,
      graph_snd,Category.id_comp]
/-- The graph-evaluated source frame equals the ORIGINAL family frame
pulled along any affine test of that family, retaining its literal path iso. -/
lemma frame_eq : frame p L F T (original p S T b t)=
    transport L t (pullback.fst p b) (original p S T b t) rfl (F.app S b) := by
  have hn := F.natural S T (coefficient p S T b t) b
    (original p S T b t ≫ p) (over p S T b t)
  change transport L (graph p T (original p S T b t))
    (pullback.fst p (original p S T b t ≫ p)) (original p S T b t)
      (graph_fst p T (original p S T b t)) (F.app T (original p S T b t ≫ p))=_
  rw [←hn,composition]
  apply arrow_congr
  exact factor p S T b t
end RelativeFamilyFrameGraphFactor318
