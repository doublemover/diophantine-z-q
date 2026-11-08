module
public import IntrinsicDifferentialPullback318
public import IntrinsicChartSections318
public import AffineChartPullbackScalars318
public section
noncomputable section
namespace IntrinsicDifferentialSectionPullback318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) {R:CommRingCat.{u}}
  (p:X⟶Spec R) (q:Y⟶Spec R) (h:f≫q=p)
  (U:Y.Opens) (V:X.Opens) (hv:V≤f ⁻¹ᵁ U)

/-- Canonical differential pullback followed by restriction to an actual subopen. -/
@[expose] def value : Γ(FamilyIntrinsicDifferentials318.omega q,U) →+
    Γ(FamilyIntrinsicDifferentials318.omega p,V) :=
  ((FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hv).op).hom.comp
    ((IntrinsicDifferentialPullback318.map f p q h).val.app (op U)).hom.toAddMonoidHom

theorem value_D (s:Γ(Y,U)) :
    value f p q h U V hv ((FamilyIntrinsicDifferentials318.D q).d s)=
      (FamilyIntrinsicDifferentials318.D p).d (f.appLE U V hv s) := by
  change (FamilyIntrinsicDifferentials318.omega p).presheaf.map _
    ((IntrinsicDifferentialPullback318.map f p q h).val.app _
      ((FamilyIntrinsicDifferentials318.D q).d s))=_
  rw [IntrinsicDifferentialPullback318.map_D]
  exact ((FamilyIntrinsicDifferentials318.D p).d_map (homOfLE hv).op (f.app U s)).symm

theorem value_smul (a:Γ(Y,U)) (s:Γ(FamilyIntrinsicDifferentials318.omega q,U)) :
    value f p q h U V hv (a • s)=f.appLE U V hv a • value f p q h U V hv s := by
  change (FamilyIntrinsicDifferentials318.omega p).presheaf.map _
    ((IntrinsicDifferentialPullback318.map f p q h).val.app _ (a • s))=_
  rw [map_smul]
  exact (FamilyIntrinsicDifferentials318.omega p).val.map_smul
    (homOfLE hv).op (f.app U a) _

/-- Pulling a restricted global section gives the restriction of its actual
whole-source pullback, for every chosen source subopen. -/
theorem globalSection_restrict (s:Γ(FamilyIntrinsicDifferentials318.omega q,⊤)) :
    value f p q h U V hv
      ((FamilyIntrinsicDifferentials318.omega q).presheaf.map (homOfLE le_top).op s)=
      (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE le_top).op
        (IntrinsicDifferentialPullback318.globalSection f p q h s) := by
  have hn:=PresheafOfModules.naturality_apply
    (IntrinsicDifferentialPullback318.map f p q h).val (homOfLE (show U≤⊤ from le_top)).op s
  change (IntrinsicDifferentialPullback318.map f p q h).val.app (op U)
      ((FamilyIntrinsicDifferentials318.omega q).presheaf.map (homOfLE le_top).op s)=
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE le_top).op
      (IntrinsicDifferentialPullback318.globalSection f p q h s) at hn
  change (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hv).op
    ((IntrinsicDifferentialPullback318.map f p q h).val.app (op U) _)=_
  rw [hn]
  exact (CategoryTheory.Functor.map_comp_apply _ _ _ _).symm

section Affine
variable {R₀ S T:Type u} [CommRing R₀] [CommRing S] [CommRing T]
    [Algebra R₀ S] [Algebra R₀ T]
    (p:X⟶Spec (CommRingCat.of R₀)) (q:Y⟶Spec (CommRingCat.of R₀)) (h:f≫q=p)
    (a:S→ₐ[R₀]T) (j:Spec (CommRingCat.of T)⟶X) [IsOpenImmersion j]
    (k:Spec (CommRingCat.of S)⟶Y) [IsOpenImmersion k]
    (hj:j≫p=Spec.map (CommRingCat.ofHom (algebraMap R₀ T)))
    (hk:k≫q=Spec.map (CommRingCat.ofHom (algebraMap R₀ S)))
    (hsquare:j≫f=Spec.map (CommRingCat.ofHom a.toRingHom)≫k)
    (hv:j ''ᵁ ⊤≤f ⁻¹ᵁ (k ''ᵁ ⊤))

include hsquare in
/-- On full actual affine chart squares, intrinsic pullback agrees exactly
with the algebraic universal-differential map, for every differential. -/
theorem sectionMap_naturality :
    (value f p q h (k ''ᵁ ⊤) (j ''ᵁ ⊤) hv).comp
      (IntrinsicChartSections318.sectionMap k q hk)=
      (IntrinsicChartSections318.sectionMap j p hj).comp
        (AlgHomDifferential318.map a).toAddMonoidHom := by
  let v:=value f p q h (k ''ᵁ ⊤) (j ''ᵁ ⊤) hv
  let aS:S→Γ(Y,k ''ᵁ ⊤):=fun s=>(k.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)
  let aT:T→Γ(X,j ''ᵁ ⊤):=fun t=>(j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of T)).inv t)
  have ha (s:S):f.appLE (k ''ᵁ ⊤) (j ''ᵁ ⊤) hv (aS s)=aT (a s):=
    AffineChartPullbackScalars318.affine_scalar (CommRingCat.ofHom a.toRingHom) f j k hsquare hv s
  apply KaehlerAdditiveExt318.ext
  · intro s
    change v (IntrinsicChartSections318.sectionMap k q hk (KaehlerDifferential.D R₀ S s))=
      IntrinsicChartSections318.sectionMap j p hj (AlgHomDifferential318.map a (KaehlerDifferential.D R₀ S s))
    rw [IntrinsicChartSections318.section_D,value_D,ha,
      AlgHomDifferential318.map_D,IntrinsicChartSections318.section_D]
  · intro s ω heq
    change v (IntrinsicChartSections318.sectionMap k q hk (s • ω))=
      IntrinsicChartSections318.sectionMap j p hj (AlgHomDifferential318.map a (s • ω))
    rw [IntrinsicChartSections318.section_smul,value_smul,ha]
    change aT (a s) • v (IntrinsicChartSections318.sectionMap k q hk ω)=_
    change v (IntrinsicChartSections318.sectionMap k q hk ω)=
      IntrinsicChartSections318.sectionMap j p hj (AlgHomDifferential318.map a ω) at heq
    rw [heq,AlgHomDifferential318.map_smul,IntrinsicChartSections318.section_smul]
end Affine
end IntrinsicDifferentialSectionPullback318
