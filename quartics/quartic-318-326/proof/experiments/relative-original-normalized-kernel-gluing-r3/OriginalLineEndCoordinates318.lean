module
public import LineSheafClass318
public import ModuleLocalGluing318
public import ModuleScalar318
public import OpenLineFrameCoordinates318
public section
noncomputable section
namespace OriginalLineEndCoordinates318
open AlgebraicGeometry CategoryTheory Opposite LineSheafClass318 ModuleLocalGluing318
universe u
variable {X : Scheme.{u}} (L : Line X) (a : L.object ⟶ L.object)
abbrev frame (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) :=
  OpenLineFrameCoordinates318.frame L.object (L.opens i) (L.frame i) V hV
@[expose] def coefficient (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) : Γ(X,V) :=
  (frame L i V hV).symm (a.app V (frame L i V hV 1))

lemma value (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) (s : Γ(L.object,V)) :
    a.app V s=coefficient L a i V hV • s := by
  let e := frame L i V hV
  have hs : s=e.symm s • e 1 := by apply e.symm.injective; simp
  apply e.symm.injective
  rw [map_smul]
  change e.symm (a.app V s)=coefficient L a i V hV * e.symm s
  calc
    e.symm (a.app V s)=e.symm (a.app V (e.symm s • e 1)) := congrArg (fun x => e.symm (a.app V x)) hs
    _ = e.symm s * coefficient L a i V hV := by rw [Scheme.Modules.Hom.app_smul,map_smul]; rfl
    _ = _ := mul_comm _ _

lemma unique (i : L.Index) (V : X.Opens) (hV : V≤L.opens i) (r : Γ(X,V))
    (h : ∀ s : Γ(L.object,V),a.app V s=r • s) : coefficient L a i V hV=r := by
  unfold coefficient
  rw [h,map_smul,LinearEquiv.symm_apply_apply,smul_eq_mul,mul_one]

lemma independent (i j : L.Index) (V : X.Opens) (hi : V≤L.opens i) (hj : V≤L.opens j) :
    coefficient L a i V hi=coefficient L a j V hj :=
  unique L a i V hi _ (value L a j V hj)

lemma natural (i : L.Index) (V W : X.Opens) (hV : V≤L.opens i) (hW : W≤V) :
    X.presheaf.map (homOfLE hW).op (coefficient L a i V hV)=
      coefficient L a i W (hW.trans hV) := by
  unfold coefficient
  rw [OpenLineFrameCoordinates318.inverse_natural]
  have hn := congrArg (fun f => f (frame L i V hV 1))
    (a.mapPresheaf.naturality (homOfLE hW).op)
  change a.app W (res L.object hW (frame L i V hV 1))=
    res L.object hW (a.app V (frame L i V hV 1)) at hn
  rw [←hn,OpenLineFrameCoordinates318.natural,map_one]
  rfl
end OriginalLineEndCoordinates318
