module
public import OpenLineFrameCoordinates318
public import FrameScalarAlgebra318
public section
noncomputable section
namespace LineFrameTransitions318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
variable {X:Scheme.{u}} (M:X.Modules) {ι:Type v} (V:ι→X.Opens)
  (frames:∀i,SheafOfModules.unit ((V i):Scheme).ringCatSheaf≅M.restrict (V i).ι)
@[expose] def scalar (i j:ι) (W:X.Opens) (hi:W≤V i) (hj:W≤V j):Γ(X,W)ˣ:=
  FrameScalarAlgebra318.scalar (OpenLineFrameCoordinates318.frame M (V i) (frames i) W hi)
    (OpenLineFrameCoordinates318.frame M (V j) (frames j) W hj)
lemma relation (i j:ι) (W:X.Opens) (hi:W≤V i) (hj:W≤V j) (s:Γ(X,W)):
    OpenLineFrameCoordinates318.frame M (V i) (frames i) W hi
      ((scalar M V frames i j W hi hj).val*s)=
    OpenLineFrameCoordinates318.frame M (V j) (frames j) W hj s:=
  FrameScalarAlgebra318.relation _ _ s
lemma unique (i j:ι) (W:X.Opens) (hi:W≤V i) (hj:W≤V j) (a:Γ(X,W)ˣ)
    (h:∀s,OpenLineFrameCoordinates318.frame M (V i) (frames i) W hi (a.val*s)=
      OpenLineFrameCoordinates318.frame M (V j) (frames j) W hj s):
    scalar M V frames i j W hi hj=a:=FrameScalarAlgebra318.unique _ _ a h
lemma restrict (i j:ι) {W Z:X.Opens} (hi:Z≤V i) (hj:Z≤V j) (h:W≤Z):
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom (scalar M V frames i j Z hi hj)=
      scalar M V frames i j W (h.trans hi) (h.trans hj):=by
  apply Units.ext
  change X.presheaf.map (homOfLE h).op
    ((OpenLineFrameCoordinates318.frame M (V i) (frames i) Z hi).symm
      (OpenLineFrameCoordinates318.frame M (V j) (frames j) Z hj 1))=_
  rw [OpenLineFrameCoordinates318.inverse_natural,OpenLineFrameCoordinates318.natural,map_one]
  rfl
lemma self (i:ι) (W:X.Opens) (hi:W≤V i):scalar M V frames i i W hi hi=1:=
  FrameScalarAlgebra318.self _
lemma comp (i j k:ι) (W:X.Opens) (hi:W≤V i) (hj:W≤V j) (hk:W≤V k):
    scalar M V frames i j W hi hj*scalar M V frames j k W hj hk=
      scalar M V frames i k W hi hk:=FrameScalarAlgebra318.comp _ _ _
end LineFrameTransitions318
