module
public import TildePullbackInverseComposition318
public import OriginalLineAffineBaseChange318
public section
noncomputable section
namespace OriginalLineComparisonComposition318
open AlgebraicGeometry CategoryTheory LineSheafClass318 OriginalLineAffineBaseChange318
set_option maxHeartbeats 1000000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) (L : Line (Spec R))

/-- The original section comparison is exactly the adjoint of the original
sheaf comparison, rather than an isomorphism chosen independently. -/
lemma sheafIso_adjoint :
    (tilde.adjunction (R := S)).homEquiv _ _ (sheafIso f L).hom =
      (sectionsIso f L).hom := by
  rw [Adjunction.homEquiv_unit]
  rfl

lemma tilde_counit (A : (Spec S).Modules) :
    (tilde.adjunction (R:=S)).counit.app A = A.fromTildeΓ := rfl

/-- Applying the original tilde-Gamma counit to the section comparison
recovers the same original sheaf comparison. -/
lemma sectionsIso_counit :
    (tilde.functor S).map (sectionsIso f L).hom ≫
      (LineSheafPullback318.line (Spec.map f) L).object.fromTildeΓ = (sheafIso f L).hom := by
  have h := congrArg ((tilde.adjunction (R := S)).homEquiv _ _).symm (sheafIso_adjoint f L)
  simpa only [Equiv.symm_apply_apply, Adjunction.homEquiv_counit,tilde_counit] using h.symm

/-- Exact naturality of original line sections under actual pullback. -/
@[reassoc] lemma sectionsIso_naturality (K : Line (Spec R)) (h : L.object ⟶ K.object) :
    (ModuleCat.extendScalars f.hom).map (moduleSpecΓFunctor.map h) ≫ (sectionsIso f K).hom =
      (sectionsIso f L).hom ≫ moduleSpecΓFunctor.map
        ((Scheme.Modules.pullback (Spec.map f)).map h) := by
  have hh := (tilde.adjunction (R:=S)).homEquiv_naturality_left_square
    ((ModuleCat.extendScalars f.hom).map (moduleSpecΓFunctor.map h))
    (sheafIso f K).hom (sheafIso f L).hom ((Scheme.Modules.pullback (Spec.map f)).map h)
    (sheafIso_naturality f L K h)
  simpa only [sheafIso_adjoint] using hh

/-- The two actual sheaf comparisons compose across the original module
and scheme composition maps. No transition or cocycle equation is assumed. -/
lemma sheaf_composition :
    (tilde.functor T).map ((ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom) ≫
      (sheafIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      (AffineComparisonMates318.pullbackComp f g).hom.app L.object =
    (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app
      (OriginalLineAffineModel318.sections R L)) ≫ (sheafIso (f ≫ g) L).hom := by
  let N := OriginalLineAffineModel318.sections R L
  let K := LineSheafPullback318.line (Spec.map f) L
  let P := Scheme.Modules.pullback (Spec.map f)
  let Q := Scheme.Modules.pullback (Spec.map g)
  let Z := Scheme.Modules.pullback (Spec.map (f ≫ g))
  let c := AffineComparisonMates318.pullbackComp f g
  let b := (TildePullback318.pullbackIso g).inv
  change (ModuleCat.extendScalars g.hom ⋙ tilde.functor T).map (sectionsIso f L).hom ≫
    (b.app (OriginalLineAffineModel318.sections S K) ≫
      Q.map K.object.fromTildeΓ) ≫ c.hom.app L.object = _
  calc
    _ = b.app ((ModuleCat.extendScalars f.hom).obj N) ≫
        Q.map ((tilde.functor S).map (sectionsIso f L).hom) ≫
        Q.map K.object.fromTildeΓ ≫ c.hom.app L.object := by
      have hn := b.naturality (sectionsIso f L).hom
      simpa only [N,K,Functor.comp_map,Category.assoc] using congrArg
        (fun k => k ≫ Q.map K.object.fromTildeΓ ≫ c.hom.app L.object) hn
    _ = b.app ((ModuleCat.extendScalars f.hom).obj N) ≫
        Q.map (sheafIso f L).hom ≫ c.hom.app L.object := by
      simpa only [K,Functor.map_comp,Category.assoc] using congrArg
        (fun k => b.app ((ModuleCat.extendScalars f.hom).obj N) ≫ Q.map k ≫ c.hom.app L.object)
        (sectionsIso_counit f L)
    _ = b.app ((ModuleCat.extendScalars f.hom).obj N) ≫
        Q.map ((TildePullback318.pullbackIso f).inv.app N) ≫
        (P ⋙ Q).map L.object.fromTildeΓ ≫ c.hom.app L.object := by
      rw [sheafIso_counit, Functor.map_comp]
      simp only [N,P,Functor.comp_map,Category.assoc]
    _ = b.app ((ModuleCat.extendScalars f.hom).obj N) ≫
        Q.map ((TildePullback318.pullbackIso f).inv.app N) ≫
        c.hom.app ((tilde.functor R).obj N) ≫ Z.map L.object.fromTildeΓ := by
      rw [c.hom.naturality]
    _ = ((tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app N) ≫
        (TildePullback318.pullbackIso (f ≫ g)).inv.app N) ≫
          Z.map L.object.fromTildeΓ := by
      simpa only [Category.assoc] using congrArg
        (fun k => k ≫ Z.map L.object.fromTildeΓ)
        (TildePullbackInverseComposition318.composition f g N)
    _ = _ := by rw [Category.assoc]; rfl

/-- Exact composition for the unchanged original line global-section maps. -/
lemma sections_composition :
    (ModuleCat.extendScalars g.hom).map (sectionsIso f L).hom ≫
      (sectionsIso g (LineSheafPullback318.line (Spec.map f) L)).hom ≫
      moduleSpecΓFunctor.map ((AffineComparisonMates318.pullbackComp f g).hom.app L.object) =
    (ModuleCat.extendScalarsComp f.hom g.hom).inv.app
      (OriginalLineAffineModel318.sections R L) ≫ (sectionsIso (f ≫ g) L).hom := by
  have h := congrArg ((tilde.adjunction (R := T)).homEquiv _ _) (sheaf_composition f g L)
  rw [Adjunction.homEquiv_naturality_left,Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right] at h
  simpa only [sheafIso_adjoint,Category.assoc] using h
end OriginalLineComparisonComposition318
