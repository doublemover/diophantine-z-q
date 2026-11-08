module
public import IntrinsicChartSections318
public section
noncomputable section
namespace IntrinsicChartNaturality318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {Y : Scheme.{u}} {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    (f : S →ₐ[R] T) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (hS : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (hT : (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap R T)))

/-- A coordinate change between actual affine open charts carries every
algebraic differential to the restriction of its intrinsic ambient section.
This uses actual sheaf restriction, actual differential pullback, and equality
on universal differentials followed by Kähler generation. -/
theorem sectionMap_naturality :
    ((FamilyIntrinsicDifferentials318.omega p).presheaf.map
      (homOfLE (OpenChartSections318.imageLE (Spec.map (CommRingCat.ofHom f.toRingHom)) j)).op).hom.comp
        (IntrinsicChartSections318.sectionMap j p hS) =
    (IntrinsicChartSections318.sectionMap (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) p hT).comp
      (AlgHomDifferential318.map f).toAddMonoidHom := by
  let k := Spec.map (CommRingCat.ofHom f.toRingHom)
  let M := FamilyIntrinsicDifferentials318.omega p
  let i := (homOfLE (OpenChartSections318.imageLE k j)).op
  let res : Γ(M,j ''ᵁ ⊤) →+ Γ(M,(k ≫ j) ''ᵁ ⊤) := (M.presheaf.map i).hom
  let aS : S → Γ(Y,j ''ᵁ ⊤) := fun s => (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)
  let aT : T → Γ(Y,(k ≫ j) ''ᵁ ⊤) := fun t => ((k ≫ j).appIso ⊤).inv
    ((Scheme.ΓSpecIso (CommRingCat.of T)).inv t)
  let F := res.comp (IntrinsicChartSections318.sectionMap j p hS)
  let G := (IntrinsicChartSections318.sectionMap (k ≫ j) p hT).comp
    (AlgHomDifferential318.map f).toAddMonoidHom
  have ha (s : S) : Y.presheaf.map i (aS s)=aT (f s) :=
    OpenChartSections318.affine_restriction (CommRingCat.ofHom f.toRingHom) j s
  change F=G
  apply KaehlerAdditiveExt318.ext
  · intro s
    have h1 := IntrinsicChartSections318.section_D j p hS s
    have h2 := IntrinsicChartSections318.section_D (k ≫ j) p hT (f s)
    have h3 := (FamilyIntrinsicDifferentials318.D p).d_map i (aS s)
    have h4 := congrArg (fun a => (FamilyIntrinsicDifferentials318.D p).d
      (X:=op ((k ≫ j) ''ᵁ ⊤)) a) (ha s)
    have h5 := congrArg (IntrinsicChartSections318.sectionMap (k ≫ j) p hT)
      (AlgHomDifferential318.map_D f s)
    exact (congrArg res h1).trans (h3.symm.trans (h4.trans (h2.symm.trans h5.symm)))
  · intro s ω heq
    have hF : F (s • ω)=aT (f s) • F ω := by
      have h1 := congrArg res (IntrinsicChartSections318.section_smul j p hS s ω)
      have h2 := M.val.map_smul i (aS s) (IntrinsicChartSections318.sectionMap j p hS ω)
      have h3 := congrArg (fun a : Γ(Y,(k ≫ j) ''ᵁ ⊤) => a • F ω) (ha s)
      exact h1.trans (h2.trans h3)
    have hG : G (s • ω)=aT (f s) • G ω := by
      have h1 := congrArg (IntrinsicChartSections318.sectionMap (k ≫ j) p hT)
        (AlgHomDifferential318.map_smul f s ω)
      exact h1.trans (IntrinsicChartSections318.section_smul (k ≫ j) p hT (f s)
        (AlgHomDifferential318.map f ω))
    exact hF.trans ((congrArg (fun t : Γ(M,(k ≫ j) ''ᵁ ⊤) => aT (f s) • t) heq).trans hG.symm)

theorem section_restrict (ω : KaehlerDifferential R S) :
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map
      (homOfLE (OpenChartSections318.imageLE (Spec.map (CommRingCat.ofHom f.toRingHom)) j)).op
      (IntrinsicChartSections318.sectionMap j p hS ω) =
    IntrinsicChartSections318.sectionMap (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j) p hT
      (AlgHomDifferential318.map f ω) :=
  congrArg (fun k => k ω) (sectionMap_naturality f j p hS hT)
/-- The same restriction identity through a specified equality of actual chart
routes. This eliminates any choice of the common chart factorization. -/
theorem section_restrict_to
    (jT : Spec (CommRingCat.of T) ⟶ Y) [IsOpenImmersion jT]
    (hC : jT ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (route : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ j=jT)
    (himage : jT ''ᵁ ⊤ ≤ j ''ᵁ ⊤) (ω : KaehlerDifferential R S) :
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE himage).op
      (IntrinsicChartSections318.sectionMap j p hS ω) =
    IntrinsicChartSections318.sectionMap jT p hC (AlgHomDifferential318.map f ω) := by
  subst jT
  exact section_restrict f j p hS hC ω

end IntrinsicChartNaturality318
