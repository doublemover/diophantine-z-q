module
public import GlobalInvariantLine318
public import CanonicalRestrictionComparison318
public section
noncomputable section
namespace InvariantTransition318
open AlgebraicGeometry CategoryTheory Opposite
open CanonicalDifferentialSheafMap318 AffineDifferentialSheaf318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- Affine pushforward global comparison is the literal underlying section identification. -/
theorem globalIso_apply {S T : CommRingCat.{u}} (f : S ⟶ T) (M : (Spec T).Modules)
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj M)) :
    (PushforwardGlobalSections318.globalIso f M).hom s=(show Γ(M,⊤) from s) := by
  rfl

/-- Equality on the genuine global unit generator determines a whole sheaf morphism. -/
theorem unitHom_ext_top {X : Scheme.{u}} (M : X.Modules)
    (f g : SheafOfModules.unit X.ringCatSheaf ⟶ M)
    (h : f.val.app (op ⊤) (show Γ(X,⊤) from 1)=g.val.app (op ⊤) (show Γ(X,⊤) from 1)) : f=g := by
  apply M.unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  have hf := PresheafOfModules.sections_property (M.unitHomEquiv f)
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  have hg := PresheafOfModules.sections_property (M.unitHomEquiv g)
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op
  change M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    (f.val.app (op ⊤) (show Γ(X,⊤) from 1)) = (M.unitHomEquiv f).val U at hf
  change M.val.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op
    (g.val.app (op ⊤) (show Γ(X,⊤) from 1)) = (M.unitHomEquiv g).val U at hg
  rw [←hf,←hg,h]

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [IsOpenImmersion (baseMap (S:=S) (T:=T))]

/-- The actual local frame after the actual restriction and canonical differential map. -/
@[expose] def restrictedFrame (e : KaehlerDifferential R S ≃ₗ[S] S) :
    SheafOfModules.unit (Spec (CommRingCat.of T)).ringCatSheaf ⟶ targetSheaf (R:=R) (T:=T) :=
  (Scheme.Modules.restrictUnitIso (baseMap (S:=S) (T:=T))).inv ≫
    (Scheme.Modules.restrictFunctor (baseMap (S:=S) (T:=T))).map (frameIso e).inv ≫
      restrictionMap (R:=R) (S:=S) (T:=T)

theorem restrictedFrame_one (e : KaehlerDifferential R S ≃ₗ[S] S)
    (ω : KaehlerDifferential R S) (hω : e ω=1) :
    (moduleSpecΓFunctor.map (restrictedFrame (T:=T) e)) (show Γ(Spec (CommRingCat.of T),⊤) from 1)=
      (tilde.isoTop (R:=CommRingCat.of T) (ModuleCat.of T (KaehlerDifferential R T))).hom
        (KaehlerDifferential.map R R S T ω) := by
  have hadj := adjoint_restrictionMap (R:=R) (S:=S) (T:=T)
  rw [Adjunction.homEquiv_unit] at hadj
  have hval := congrArg (fun f => f.val.app (op ⊤)
    ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ω)) hadj
  have hn := global_image (R:=R) (S:=S) (T:=T) ω
  rw [globalIso_apply] at hn
  have he := UnitLineDifferentials318.frame_inverse_one (R:=R) (S:=S) e ω hω
  let U := baseMap (S:=S) (T:=T) ''ᵁ ⊤
  have heRestr := congrArg (fun g => g (show Γ(Spec (CommRingCat.of S),⊤) from 1))
    ((frameIso e).inv.val.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
  change (frameIso e).inv.val.app (op U)
      (((Spec (CommRingCat.of S)).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom 1)=
    (sourceSheaf (R:=R) (S:=S)).val.map (homOfLE (show U ≤ ⊤ from le_top)).op
      ((moduleSpecΓFunctor.map (frameIso e).inv) (show Γ(Spec (CommRingCat.of S),⊤) from 1)) at heRestr
  rw [map_one,he] at heRestr
  change (restrictionMap (R:=R) (S:=S) (T:=T)).val.app (op ⊤)
    ((sourceSheaf (R:=R) (S:=S)).val.map (homOfLE (show U ≤ ⊤ from le_top)).op
      ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ω))=_ at hval
  change (restrictionMap (R:=R) (S:=S) (T:=T)).val.app (op ⊤)
    ((frameIso e).inv.val.app (op U)
      (((baseMap (S:=S) (T:=T)).appIso ⊤).inv.hom 1))=_
  rw [map_one,heRestr]
  exact hval.trans hn

section Along
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Actual frame transport along a specified algebra homomorphism, retaining its
precise induced scalar structure and genuine canonical differential morphism. -/
@[expose] def along (f : A →ₐ[R] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (e : KaehlerDifferential R A ≃ₗ[A] A) :
    SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf ⟶
      differentialSheaf (R:=R) (S:=B) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact restrictedFrame (T:=B) e

theorem along_one (f : A →ₐ[R] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (e : KaehlerDifferential R A ≃ₗ[A] A) (ω : KaehlerDifferential R A) (hω : e ω=1) :
    (moduleSpecΓFunctor.map (along f e)) (show Γ(Spec (CommRingCat.of B),⊤) from 1)=
      (tilde.isoTop (R:=CommRingCat.of B) (ModuleCat.of B (KaehlerDifferential R B))).hom
        (AlgHomDifferential318.map f ω) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact restrictedFrame_one (T:=B) e ω hω

/-- These are genuine sheaf isomorphisms: the proved open immersion supplies
formal etaleness, and the canonical differential restriction is invertible. -/
theorem along_isIso (f : A →ₐ[R] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (e : KaehlerDifferential R A ≃ₗ[A] A) : IsIso (along f e) := by
  letI : Algebra A B := f.toRingHom.toAlgebra
  letI : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  have he : f.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P:=@Etale) (φ:=CommRingCat.ofHom f.toRingHom)).mp inferInstance
  letI : Algebra.FormallyEtale A B := he.formallyEtale
  letI := CanonicalRestrictionComparison318.canonical_restriction_isIso (R:=R) (S:=A) (T:=B)
  change IsIso ((Scheme.Modules.restrictUnitIso (baseMap (S:=A) (T:=B))).inv ≫
    (Scheme.Modules.restrictFunctor (baseMap (S:=A) (T:=B))).map (frameIso e).inv ≫
      restrictionMap (R:=R) (S:=A) (T:=B))
  infer_instance

/-- Agreement of actual invariant forms implies equality of the entire genuine
restricted sheaf-frame morphisms, not only equality on one chosen section. -/
theorem along_eq_of_generators {C : Type u} [CommRing C] [Algebra R C]
    (f : A →ₐ[R] C) (g : B →ₐ[R] C)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom))]
    (eA : KaehlerDifferential R A ≃ₗ[A] A) (eB : KaehlerDifferential R B ≃ₗ[B] B)
    (ωA : KaehlerDifferential R A) (ωB : KaehlerDifferential R B)
    (hA : eA ωA=1) (hB : eB ωB=1)
    (hω : AlgHomDifferential318.map f ωA=AlgHomDifferential318.map g ωB) :
    along f eA=along g eB := by
  apply unitHom_ext_top
  change (moduleSpecΓFunctor.map (along f eA)) (show Γ(Spec (CommRingCat.of C),⊤) from 1)=
    (moduleSpecΓFunctor.map (along g eB)) (show Γ(Spec (CommRingCat.of C),⊤) from 1)
  rw [along_one f eA ωA hA,along_one g eB ωB hB,hω]
end Along

end InvariantTransition318
