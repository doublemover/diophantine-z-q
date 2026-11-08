module
public import FamilyIntrinsicDifferentials318
public section
noncomputable section
namespace IntrinsicDifferentialPullback318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
  (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (h : f ≫ q=p)

include h in
theorem coefficients_app (U:Y.Opens) :
    (FamilyIntrinsicDifferentials318.coefficients q).app (op U) ≫ f.app U =
      (FamilyIntrinsicDifferentials318.coefficients p).app (op (f ⁻¹ᵁ U)) := by
  subst p
  change ((_ ≫ q.appTop) ≫ Y.presheaf.map (homOfLE le_top).op) ≫ f.app U =
    (_ ≫ (f ≫ q).appTop) ≫ X.presheaf.map (homOfLE le_top).op
  rw [Category.assoc,f.naturality,Scheme.Hom.comp_appTop]
  simp only [Category.assoc]
  rfl

/-- Push the actual source universal derivation along an arbitrary morphism
with its exact structure square. No open or etale hypothesis is imposed. -/
@[expose] def derivation :
    Derivation' ((Scheme.Modules.pushforward f).obj
      (FamilyIntrinsicDifferentials318.omega p)).val
        (FamilyIntrinsicDifferentials318.coefficients q) where
  d {U} := ((FamilyIntrinsicDifferentials318.D p).d
    (X:=op (f ⁻¹ᵁ U.unop))).comp (f.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change (FamilyIntrinsicDifferentials318.D p).d (f.app U.unop (a*b)) = _
    rw [map_mul,Derivation.d_mul]
    rfl
  d_map {U V} i a := by
    change (FamilyIntrinsicDifferentials318.D p).d (f.app V.unop (Y.presheaf.map i a)) =
      (FamilyIntrinsicDifferentials318.omega p).val.map
        ((TopologicalSpace.Opens.map f.base).op.map i)
          ((FamilyIntrinsicDifferentials318.D p).d (f.app U.unop a))
    have hn := congrArg (fun k => k a) (f.naturality i)
    exact (congrArg (fun z => (FamilyIntrinsicDifferentials318.D p).d
      (X:=op (f ⁻¹ᵁ V.unop)) z) hn).trans
        ((FamilyIntrinsicDifferentials318.D p).d_map
          ((TopologicalSpace.Opens.map f.base).op.map i) (f.app U.unop a))
  d_app {U} a := by
    change (FamilyIntrinsicDifferentials318.D p).d
      (f.app U.unop ((FamilyIntrinsicDifferentials318.coefficients q).app U a))=0
    have hc:=congrArg (fun k=>k a) (coefficients_app f p q h U.unop)
    exact (congrArg (fun z=>(FamilyIntrinsicDifferentials318.D p).d
      (X:=op (f ⁻¹ᵁ U.unop)) z) hc).trans
        ((FamilyIntrinsicDifferentials318.D p).d_app a)

/-- The canonical actual differential morphism, in pushforward form. -/
@[expose] def map : FamilyIntrinsicDifferentials318.omega q ⟶
    (Scheme.Modules.pushforward f).obj (FamilyIntrinsicDifferentials318.omega p) :=
  UniversalSheafDifferentials318.desc _ (derivation f p q h)

theorem map_D (U:Y.Opens) (s:Γ(Y,U)) :
    (map f p q h).val.app (op U) ((FamilyIntrinsicDifferentials318.D q).d s)=
      (FamilyIntrinsicDifferentials318.D p).d (f.app U s) :=
  Derivation.congr_d (UniversalSheafDifferentials318.desc_fac _ (derivation f p q h)) s

/-- Its genuine pullback adjoint is a morphism into the intrinsic source Omega. -/
@[expose] def pullbackMap : (Scheme.Modules.pullback f).obj
    (FamilyIntrinsicDifferentials318.omega q) ⟶ FamilyIntrinsicDifferentials318.omega p :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm (map f p q h)

theorem pullbackMap_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackMap f p q h)=
      map f p q h :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

/-- Pullback on actual global differential sections, without generic localization. -/
@[expose] def globalSection
    (s:Γ(FamilyIntrinsicDifferentials318.omega q,⊤)) :
    Γ(FamilyIntrinsicDifferentials318.omega p,⊤) :=
  (map f p q h).val.app (op ⊤) s

theorem globalSection_D (s:Γ(Y,⊤)) :
    globalSection f p q h ((FamilyIntrinsicDifferentials318.D q).d s)=
      (FamilyIntrinsicDifferentials318.D p).d (f.appTop s) := map_D f p q h ⊤ s
end IntrinsicDifferentialPullback318
