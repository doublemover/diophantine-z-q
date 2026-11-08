module
public import CompletedCharacterNormIndependence318
public section
noncomputable section
namespace CompletedCharacterLineClassNorm318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open CompletedCharacterSchemeMaps318 CompletedCharacterNormLine318
set_option maxHeartbeats 450000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
/-- Actual source-module isomorphism, with no equality of chosen presentations,
gives actual isomorphism of each unchanged constructed complementary norm line. -/
lemma respects (i:Fin 4) {L K:Line Model} (h:Related L K):
    Related (CompletedCharacterNormLine318.line i L) (CompletedCharacterNormLine318.line i K):=by
  obtain ⟨e⟩:=h
  exact ⟨CompletedCharacterNormIndependence318.lineIso i e⟩
/-- Four genuine norm functions on the existing original line-sheaf
isomorphism classes. Multiplicative/unit laws are separate consumers. -/
@[expose] def norm (i:Fin 4):Class Model→Class (Target i):=
  Quotient.map (CompletedCharacterNormLine318.line i) (fun _ _ h=>respects i h)
lemma norm_classOf (i:Fin 4) (L:Line Model):
    norm i (classOf L)=classOf (CompletedCharacterNormLine318.line i L):=rfl
lemma presentation_independent (i:Fin 4) {L K:Line Model} (e:L.object≅K.object):
    norm i (classOf L)=norm i (classOf K):=
  classOf_eq (CompletedCharacterNormIndependence318.lineIso i e)
/-- Equality of the original source classes is the actual quotient relation;
no source or target Picard variety is being identified here. -/
lemma eq_of_source_class_eq (i:Fin 4) {L K:Line Model} (h:classOf L=classOf K):
    norm i (classOf L)=norm i (classOf K):=congrArg (norm i) h
end CompletedCharacterLineClassNorm318
