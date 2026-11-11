module
public import LinearIsoFrameScalar318
public import OpenLineFrameCoordinates318
public import LineFrameTransitions318
public section
noncomputable section
namespace LineIsoRegularScalars318
open AlgebraicGeometry CategoryTheory Opposite
universe u v
variable {X : Scheme.{u}} {M N : X.Modules} (E : M ≅ N)
  {ι : Type v} (U V : ι → X.Opens)
  (e : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (d : ∀ i,SheafOfModules.unit (V i).toScheme.ringCatSheaf ≅ N.restrict (V i).ι)

@[expose] def sectionIso (W : X.Opens) : Γ(M,W) ≃ₗ[Γ(X,W)] Γ(N,W) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (op W)).mapIso E).toLinearEquiv

/-- A genuine invertible REGULAR section on every common subopen,
extracted from the entire original sheaf isomorphism. -/
@[expose] def scalar (i : ι) (W : X.Opens) (hU : W ≤ U i) (hV : W ≤ V i) : Γ(X,W)ˣ :=
  LinearIsoFrameScalar318.scalar (sectionIso E W)
    (OpenLineFrameCoordinates318.frame M (U i) (e i) W hU)
    (OpenLineFrameCoordinates318.frame N (V i) (d i) W hV)

lemma scalar_value (i : ι) (W : X.Opens) (hU : W ≤ U i) (hV : W ≤ V i) :
    (scalar E U V e d i W hU hV).val=
      (OpenLineFrameCoordinates318.frame N (V i) (d i) W hV).symm
        (E.hom.app W (OpenLineFrameCoordinates318.frame M (U i) (e i) W hU 1)) := rfl

lemma equation (i : ι) (W : X.Opens) (hU : W ≤ U i) (hV : W ≤ V i) (s : Γ(X,W)) :
    OpenLineFrameCoordinates318.frame N (V i) (d i) W hV
      ((scalar E U V e d i W hU hV).val*s)=
        E.hom.app W (OpenLineFrameCoordinates318.frame M (U i) (e i) W hU s) :=
  LinearIsoFrameScalar318.relation _ _ _ s

/-- The scalar units restrict along the ORIGINAL structure-sheaf maps. -/
lemma restrict (i : ι) {W Z : X.Opens} (hU : Z ≤ U i) (hV : Z ≤ V i) (h : W ≤ Z) :
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
      (scalar E U V e d i Z hU hV)=scalar E U V e d i W (h.trans hU) (h.trans hV) := by
  apply Units.ext
  change X.presheaf.map (homOfLE h).op (scalar E U V e d i Z hU hV).val=_
  rw [scalar_value,OpenLineFrameCoordinates318.inverse_natural]
  have hn := congrArg (fun g => g
      (OpenLineFrameCoordinates318.frame M (U i) (e i) Z hU 1))
    (E.hom.mapPresheaf.naturality (homOfLE h).op)
  change E.hom.app W (M.presheaf.map (homOfLE h).op
      (OpenLineFrameCoordinates318.frame M (U i) (e i) Z hU 1))=
    N.presheaf.map (homOfLE h).op
      (E.hom.app Z (OpenLineFrameCoordinates318.frame M (U i) (e i) Z hU 1)) at hn
  rw [←hn,OpenLineFrameCoordinates318.natural,map_one]
  rfl

/-- Whole-ring compatibility on EVERY common subopen, before complex
specialization. Both actual source and target frame cocycles appear. -/
lemma transition (i j : ι) (W : X.Opens)
    (hi : W ≤ U i) (hj : W ≤ U j) (ki : W ≤ V i) (kj : W ≤ V j) :
    scalar E U V e d i W hi ki * LineFrameTransitions318.scalar M U e i j W hi hj=
      LineFrameTransitions318.scalar N V d i j W ki kj * scalar E U V e d j W hj kj :=
  LinearIsoFrameScalar318.transition (sectionIso E W)
    (OpenLineFrameCoordinates318.frame M (U i) (e i) W hi)
    (OpenLineFrameCoordinates318.frame N (V i) (d i) W ki)
    (OpenLineFrameCoordinates318.frame M (U j) (e j) W hj)
    (OpenLineFrameCoordinates318.frame N (V j) (d j) W kj)
end LineIsoRegularScalars318
