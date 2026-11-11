module
public import FramedLineInverse318
public import ModuleLocalGluing318
public section
noncomputable section
namespace FramedSectionInverseIdealMap318
open AlgebraicGeometry CategoryTheory
open OpenLineFrameCoordinates318
universe u
variable {X : Scheme.{u}} (L : LineSheafClass318.Line X)
  (c : ∀ i,Γ(X,L.opens i))
  (hc : ∀ i j,X.presheaf.map (homOfLE inf_le_left).op (c i)=
    ((LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j).val*
      X.presheaf.map (homOfLE inf_le_right).op (c j))
abbrev inverse := FramedLineInverse318.inverse L
abbrev O := SheafOfModules.unit X.ringCatSheaf
abbrev localFrame (i : L.Index) (W : X.Opens) (hW : W≤L.opens i) :=
  frame (inverse L).object (L.opens i) ((inverse L).frame i) W hW
@[expose] def localMap (i : L.Index) (W : X.Opens) (hW : W≤L.opens i) :
    Γ((inverse L).object,W) →ₗ[Γ(X,W)] Γ(X,W) where
  toFun s := X.presheaf.map (homOfLE hW).op (c i)*(localFrame L i W hW).symm s
  map_add' s t := by rw [map_add,mul_add]
  map_smul' a s := by rw [map_smul]; change _=a*_; ring
lemma local_natural (i : L.Index) (V W : X.Opens) (hV : V≤L.opens i) (hW : W≤V)
    (s : Γ((inverse L).object,V)) :
    X.presheaf.map (homOfLE hW).op (localMap L c i V hV s)=
      localMap L c i W (hW.trans hV) ((inverse L).object.presheaf.map (homOfLE hW).op s) := by
  change X.presheaf.map (homOfLE hW).op (_*_)=_ * _
  rw [map_mul,OpenLineFrameCoordinates318.inverse_natural]
  congr 1
  exact (CategoryTheory.Functor.map_comp_apply X.presheaf (homOfLE hV).op (homOfLE hW).op (c i)).symm
include hc in
lemma local_compatible (i j : L.Index) (W : X.Opens) (hi : W≤L.opens i) (hj : W≤L.opens j)
    (s : Γ((inverse L).object,W)) : localMap L c i W hi s=localMap L c j W hj s := by
  let h : W≤L.opens i⊓L.opens j := le_inf hi hj
  let t := Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
    ((LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j)
  have hcoeff : X.presheaf.map (homOfLE hi).op (c i)=
      t.val*X.presheaf.map (homOfLE hj).op (c j) := by
    have he := congrArg (X.presheaf.map (homOfLE h).op) (hc i j)
    rw [map_mul] at he
    simpa only [t,Units.coe_map,←CategoryTheory.Functor.map_comp_apply] using he
  have he := LineFrameCocycle318.relation (inverse L).object L.opens (inverse L).frame i j W h
    ((localFrame L j W hj).symm s)
  rw [LineSheafInverse318.original_inverse_transitions] at he
  have ht : X.presheaf.map (homOfLE h).op
      (((LineFrameCocycle318.cocycle L.object L.opens L.frame).transition i j)⁻¹).val=(t⁻¹).val := by
    exact congrArg Units.val ((Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom).map_inv _)
  simp only [UnitCocycleInverse318.transition,ht,LinearEquiv.apply_symm_apply] at he
  change localFrame L i W hi ((t⁻¹).val*(localFrame L j W hj).symm s)=s at he
  have hinv := congrArg (localFrame L i W hi).symm he
  rw [LinearEquiv.symm_apply_apply] at hinv
  change _=(localFrame L i W hi).symm s at hinv
  change _*_=_*_
  rw [hcoeff,←hinv]
  calc
    (t.val*X.presheaf.map (homOfLE hj).op (c j))*
        ((t⁻¹).val*(localFrame L j W hj).symm s)=
      (t.val*(t⁻¹).val)*(X.presheaf.map (homOfLE hj).op (c j)*
        (localFrame L j W hj).symm s) := by ring
    _ = _ := by rw [Units.mul_inv,one_mul]
@[expose] def localData : ModuleLocalGluing318.LocalData (inverse L).object O L.opens where
  map := localMap L c
  natural := local_natural L c
  compatible := local_compatible L c hc

/-- The true inverse-line multiplication map, glued from complete
regular frame coefficients on all subopens. -/
@[expose] def hom : (inverse L).object ⟶ O := ModuleLocalGluing318.hom (localData L c hc) L.cover
lemma hom_subopen (i : L.Index) (W : X.Opens) (hW : W≤L.opens i)
    (s : Γ((inverse L).object,W)) :
    (hom L c hc).app W s=localMap L c i W hW s := by
  have he := ModuleLocalGluing318.value_subopen (localData L c hc) L.cover W W le_rfl i hW s
  simpa only [ModuleLocalGluing318.res_self] using he
lemma hom_frame (i : L.Index) (W : X.Opens) (hW : W≤L.opens i) (r : Γ(X,W)) :
    (hom L c hc).app W (localFrame L i W hW r)=X.presheaf.map (homOfLE hW).op (c i)*r := by
  rw [hom_subopen]
  exact congrArg (fun a => X.presheaf.map (homOfLE hW).op (c i)*a)
    ((localFrame L i W hW).symm_apply_apply r)
end FramedSectionInverseIdealMap318
