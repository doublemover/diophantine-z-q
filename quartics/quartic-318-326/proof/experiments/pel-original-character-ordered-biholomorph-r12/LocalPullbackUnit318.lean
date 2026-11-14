module
public import RestrictionPullbackCoherence318
public section
noncomputable section
namespace LocalPullbackUnit318
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z:Scheme.{u}} (f:X⟶Y)
/-- The actual adjunction unit on an ARBITRARY base open. Local sections
are never required to extend to global sections of the base module. -/
@[expose] def pull(M:Y.Modules)(U:Y.Opens):
    Γ(M,U)→+Γ((Scheme.Modules.pullback f).obj M,f⁻¹ᵁU):=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U).hom
/-- Semilinearity uses the SAME original structure map on the entire
base open, not an independently selected scalar extension. -/
lemma pull_smul(M:Y.Modules)(U:Y.Opens)(a:Γ(Y,U))(s:Γ(M,U)):
    pull f M U (a • s)=f.app U a • pull f M U s:=
  (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app (op U)).hom.map_smul a s
lemma naturality {M N:Y.Modules}(a:M⟶N)(U:Y.Opens)(s:Γ(M,U)):
    ((Scheme.Modules.pullback f).map a).app (f⁻¹ᵁU) (pull f M U s)=
      pull f N U (a.app U s):=by
  exact (congrArg (fun q=>q.app U s)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a)).symm
lemma adjoint {M:Y.Modules}{N:X.Modules}
    (a:(Scheme.Modules.pullback f).obj M⟶N)(U:Y.Opens)(s:Γ(M,U)):
    a.app (f⁻¹ᵁU) (pull f M U s)=
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ a).app U s:=by
  rw [Adjunction.homEquiv_unit]
  rfl
/-- The actual adjoint evaluation followed by genuine source restriction.
This fixes the map on a local pulled generator before computing any
coefficient in a chosen source or target frame. -/
lemma adjoint_subopen {M:Y.Modules}{N:X.Modules}
    (a:(Scheme.Modules.pullback f).obj M⟶N)(U:Y.Opens)(V:X.Opens)
    (h:V≤f⁻¹ᵁU)(s:Γ(M,U)):
    a.app V (((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE h).op
      (pull f M U s))=
    N.presheaf.map (homOfLE h).op
      (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ a).app U s):=by
  have hn:=PresheafOfModules.naturality_apply a.val (homOfLE h).op (pull f M U s)
  change a.app V (((Scheme.Modules.pullback f).obj M).presheaf.map _
    (pull f M U s))=N.presheaf.map _ (a.app (f⁻¹ᵁU) (pull f M U s)) at hn
  rw [adjoint] at hn
  exact hn
variable (g:Y⟶Z)
/-- The genuine pullback associator transports iterated LOCAL units to
the unit of the actual composite, on every original open. -/
lemma composition(M:Z.Modules)(U:Z.Opens)(s:Γ(M,U)):
    ((Scheme.Modules.pullbackComp f g).hom.app M).app ((f≫g)⁻¹ᵁU)
      (pull f ((Scheme.Modules.pullback g).obj M) (g⁻¹ᵁU) (pull g M U s))=
        pull (f≫g) M U s:=by
  have h:=unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f≫g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at h
  have hs:=congrArg (fun q=>q.app U s) h
  change pull f ((Scheme.Modules.pullback g).obj M) (g⁻¹ᵁU) (pull g M U s)=
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f≫g)⁻¹ᵁU)
      (pull (f≫g) M U s) at hs
  rw [hs]
  exact congrArg (fun q=>q.app ((f≫g)⁻¹ᵁU) (pull (f≫g) M U s))
    ((Scheme.Modules.pullbackComp f g).inv_hom_id_app M)

section Open
variable [IsOpenImmersion f]
/-- Whole sheaf-morphism normalization. This is the original adjunction
uniqueness identity, not a statement restricted to global sections. -/
lemma restriction_unit(M:Y.Modules):
    (Scheme.Modules.restrictAdjunction f).unit.app M≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M)=
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M:=by
  have h:=RestrictionPullbackCoherence318.adjoint_restrict_component f M
  simpa only [Adjunction.homEquiv_unit] using h
lemma restriction_unit_inverse(M:Y.Modules):
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M)=
      (Scheme.Modules.restrictAdjunction f).unit.app M:=by
  rw [←restriction_unit f M,Category.assoc,←Functor.map_comp]
  simp only [Iso.hom_inv_id_app,Functor.map_id,Category.comp_id]
/-- The inverse canonical comparison sends a local pulled section to
its actual restriction on the full image/preimage intersection. -/
lemma open_inverse(M:Y.Modules)(U:Y.Opens)(s:Γ(M,U)):
    ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M).app (f⁻¹ᵁU)
      (pull f M U s)=M.presheaf.map (homOfLE (f.image_preimage_le U)).op s:=by
  exact congrArg (fun q=>q.app U s) (restriction_unit_inverse f M)
lemma open_forward(M:Y.Modules)(U:Y.Opens)(s:Γ(M,U)):
    ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M).app (f⁻¹ᵁU)
      (M.presheaf.map (homOfLE (f.image_preimage_le U)).op s)=pull f M U s:=by
  exact congrArg (fun q=>q.app U s) (restriction_unit f M)
end Open
end LocalPullbackUnit318
