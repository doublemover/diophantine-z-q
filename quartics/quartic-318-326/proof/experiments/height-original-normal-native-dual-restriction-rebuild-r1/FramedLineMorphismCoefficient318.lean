module
public import LineFrameCocycle318
public import ModuleLocalGluing318
public section
noncomputable section
namespace FramedLineMorphismCoefficient318
open AlgebraicGeometry CategoryTheory Opposite
universe u
variable {X:Scheme.{u}} {ι:Type u} (M N:X.Modules) (U:ι→X.Opens)
  (e:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅M.restrict (U i).ι)
  (f:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅N.restrict (U i).ι)
  (d:M⟶N)
abbrev coordinates(i:ι)(V:X.Opens)(h:V≤U i):=
  (OpenLineFrameCoordinates318.frame M (U i) (e i) V h).symm
@[expose] def coefficient(i:ι)(V:X.Opens)(h:V≤U i):Γ(X,V):=
  (OpenLineFrameCoordinates318.frame N (U i) (f i) V h).symm
    (d.app V ((OpenLineFrameCoordinates318.frame M (U i) (e i) V h) 1))
/-- The matrix coefficient is extracted from the ACTUAL sheaf morphism.
Its full action on every section is then derived by original linearity. -/
lemma action(i:ι)(V:X.Opens)(h:V≤U i)(s:Γ(M,V)):
    (OpenLineFrameCoordinates318.frame N (U i) (f i) V h).symm (d.app V s)=
      coefficient M N U e f d i V h*coordinates M U e i V h s:=by
  let a:=OpenLineFrameCoordinates318.frame M (U i) (e i) V h
  have hs:s=(coordinates M U e i V h s) • a 1:=by
    rw [←map_smul,smul_eq_mul,mul_one]
    exact (a.apply_symm_apply s).symm
  calc
    _=(OpenLineFrameCoordinates318.frame N (U i) (f i) V h).symm
        (d.app V ((coordinates M U e i V h s) • a 1)):=congrArg _ (congrArg (d.app V) hs)
    _=coordinates M U e i V h s*
        (OpenLineFrameCoordinates318.frame N (U i) (f i) V h).symm (d.app V (a 1)):=by
      rw [map_smul,map_smul,smul_eq_mul]
    _=coefficient M N U e f d i V h*coordinates M U e i V h s:=mul_comm _ _
lemma natural(i:ι)(V W:X.Opens)(hV:V≤U i)(hW:W≤V):
    X.presheaf.map (homOfLE hW).op (coefficient M N U e f d i V hV)=
      coefficient M N U e f d i W (hW.trans hV):=by
  unfold coefficient
  rw [OpenLineFrameCoordinates318.inverse_natural]
  have hd:=PresheafOfModules.naturality_apply d.val (homOfLE hW).op
    ((OpenLineFrameCoordinates318.frame M (U i) (e i) V hV) 1)
  rw [←hd,OpenLineFrameCoordinates318.natural,map_one]
lemma coordinate_transition {P:X.Modules}
    (g:∀i,SheafOfModules.unit (U i).toScheme.ringCatSheaf≅P.restrict (U i).ι)
    (i j:ι)(V:X.Opens)(hi:V≤U i)(hj:V≤U j)(s:Γ(P,V)):
    (OpenLineFrameCoordinates318.frame P (U i) (g i) V hi).symm s=
      X.presheaf.map (homOfLE (le_inf hi hj)).op
        ((LineFrameCocycle318.cocycle P U g).transition i j).val*
        (OpenLineFrameCoordinates318.frame P (U j) (g j) V hj).symm s:=by
  have h:=LineFrameCocycle318.relation P U g i j V (le_inf hi hj)
    ((OpenLineFrameCoordinates318.frame P (U j) (g j) V hj).symm s)
  rw [LinearEquiv.apply_symm_apply] at h
  apply (OpenLineFrameCoordinates318.frame P (U i) (g i) V hi).injective
  rw [LinearEquiv.apply_symm_apply]
  exact h.symm
/-- Exact FULL-overlap change-of-frame identity. In particular the
coefficient transforms as target/source, while its evaluation line
transforms as source/target. No pointwise or generic equality suffices. -/
lemma transition(i j:ι)(V:X.Opens)(hi:V≤U i)(hj:V≤U j):
    coefficient M N U e f d i V hi*
      X.presheaf.map (homOfLE (le_inf hi hj)).op
        ((LineFrameCocycle318.cocycle M U e).transition i j).val=
      X.presheaf.map (homOfLE (le_inf hi hj)).op
        ((LineFrameCocycle318.cocycle N U f).transition i j).val*
          coefficient M N U e f d j V hj:=by
  let s:Γ(M,V):=(OpenLineFrameCoordinates318.frame M (U j) (e j) V hj) 1
  have hs:=coordinate_transition U e i j V hi hj s
  simp only [s,LinearEquiv.symm_apply_apply,mul_one] at hs
  have ht:=coordinate_transition U f i j V hi hj (d.app V s)
  rw [action M N U e f d i V hi s] at ht
  change coefficient M N U e f d i V hi*
    (OpenLineFrameCoordinates318.frame M (U i) (e i) V hi).symm s=_ at ht
  rw [hs] at ht
  exact ht
end FramedLineMorphismCoefficient318
