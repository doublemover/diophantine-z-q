module
public import ModuleLocalIsomorphism318
public section
noncomputable section
namespace ModuleOpenIsoCriterion318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open ModuleLocalGluing318
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X:Scheme.{u}} {M N:X.Modules} (φ:M⟶N)
lemma app_isIso (U:X.Opens) [IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ)]
    (W:X.Opens) (hW:W≤U):IsIso (φ.app W):=by
  have h:IsIso (((Scheme.Modules.restrictFunctor U.ι).map φ).app (U.ι⁻¹ᵁW)):=inferInstance
  change IsIso (φ.app (U.ι ''ᵁ(U.ι⁻¹ᵁW))) at h
  have he:U.ι ''ᵁ(U.ι⁻¹ᵁW)=W:=by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf,Scheme.Opens.opensRange_ι,inf_eq_right.mpr hW]
  exact (congrArg (fun O => IsIso (φ.app O)) he).mp h
variable {ι:Type u} (U:ι→X.Opens)
@[expose] def data:LocalData M N U where
  map _ W _ :=(φ.val.app (op W)).hom
  natural _ V W _ hW s:=by
    exact (congrArg (fun g=>g s) (φ.mapPresheaf.naturality (homOfLE hW).op)).symm
  compatible _ _ _ _ _ _:=rfl
lemma glued_eq (hc:⊤ ≤ iSup U):ModuleLocalGluing318.hom (data φ U) hc=φ:=by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  change value (data φ U) hc W s=φ.app W s
  apply ext_value hc W
  intro i
  rw [value_restrict]
  change φ.mapPresheaf.app (op (W⊓U i)) (M.presheaf.map (homOfLE inf_le_left).op s)=
    N.presheaf.map (homOfLE inf_le_left).op (φ.mapPresheaf.app (op W) s)
  exact congrArg (fun g=>g s) (φ.mapPresheaf.naturality
    (homOfLE (show W⊓U i≤W from inf_le_left)).op)
/-- Genuine local isomorphisms on a covering family give an isomorphism of
the original module sheaves, with the original map retained exactly. -/
lemma of_restrictions (hc:⊤ ≤ iSup U)
    (h:∀i,IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map φ)):IsIso φ:=by
  have hb (i:ι) (W:X.Opens) (hW:W≤U i):Function.Bijective ((data φ U).map i W hW):=by
    letI:=h i
    letI:=app_isIso φ (U i) W hW
    exact ConcreteCategory.bijective_of_isIso (φ.app W)
  have he: (ModuleLocalIsomorphism318.iso (data φ U) hc hb).hom=φ:=glued_eq φ U hc
  rw [←he]
  infer_instance
end ModuleOpenIsoCriterion318
