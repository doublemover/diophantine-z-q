module
public import ActualTwoDescentOriginalRootLocalFrameCoefficient318
public section
noncomputable section
namespace ActualTwoDescentTildeStructureNormalization318
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {R : Type u} [CommRing R]

lemma isoTop_one :
    (tilde.isoTop (R:=CommRingCat.of R) (ModuleCat.of R R)).hom 1=
      (1 : Γ(Spec (CommRingCat.of R),⊤)) := by
  change StructureSheaf.const (1:R) (1:R) ⊤ (by simp)=1
  exact StructureSheaf.const_one ⊤

/-- The canonical tilde-self normalization is the actual Gamma-Spec
ring normalization,not a freely chosen linear identification. -/
lemma isoTop_ring (r : R) :
    (tilde.isoTop (R:=CommRingCat.of R) (ModuleCat.of R R)).hom r=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv r := by
  have h := (tilde.isoTop (R:=CommRingCat.of R) (ModuleCat.of R R)).hom.hom.map_smul r (1:R)
  rw [smul_eq_mul,mul_one,isoTop_one] at h
  rw [Scheme.Modules.smul_Spec_def] at h
  change _=((Spec (CommRingCat.of R)).presheaf.map (𝟙 (op ⊤))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))*1 at h
  simpa only [Functor.map_id,ConcreteCategory.id_apply,mul_one] using h

/-- Actual sheaf morphisms out of an affine tilde are detected by ALL
ordinary module elements under the native adjunction unit. -/
lemma tilde_hom_ext (M : ModuleCat R) {N : (Spec (CommRingCat.of R)).Modules}
    {f g : tilde M ⟶ N}
    (h : ∀ x, f.app ⊤ ((tilde.isoTop M).hom x)=g.app ⊤ ((tilde.isoTop M).hom x)) : f=g := by
  apply ((tilde.adjunction (R:=CommRingCat.of R)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit,Adjunction.homEquiv_unit]
  ext x
  exact h x

lemma unit_hom_ext {X : Scheme.{u}} {M : X.Modules}
    {f g : SheafOfModules.unit X.ringCatSheaf ⟶ M}
    (h : ∀ U, f.app U (1:Γ(X,U))=g.app U 1) : f=g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext a
  have hf := (f.app U).hom.map_smul a (1:Γ(X,U))
  have hg := (g.app U).hom.map_smul a (1:Γ(X,U))
  simpa only [smul_eq_mul,mul_one] using hf.trans ((congrArg (a • ·) (h U)).trans hg.symm)

lemma restrictUnit_adjoint {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (Scheme.Modules.restrictAdjunction j).homEquiv _ _
      (Scheme.Modules.restrictUnitIso j).hom=StructurePushforwardSplit318.unitMap j := by
  apply unit_hom_ext
  intro U
  rw [Adjunction.homEquiv_unit]
  change (j.appIso (j⁻¹ᵁ U)).hom
    (Y.presheaf.map (homOfLE (j.image_preimage_le U)).op (1:Γ(Y,U)))=j.app U 1
  simp only [map_one]

lemma structure_global {S : CommRingCat.{u}} (f : CommRingCat.of R ⟶ S) (r : R) :
    (PushforwardGlobalSections318.globalIso f (SheafOfModules.unit (Spec S).ringCatSheaf)).hom
      ((moduleSpecΓFunctor.map (StructurePushforwardSplit318.unitMap (Spec.map f)))
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))=(Scheme.ΓSpecIso S).inv (f r) := by
  change (Spec.map f).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)=_
  exact (congrArg (fun k => k r) (Scheme.ΓSpecIso_inv_naturality f)).symm

lemma pushforward_global_natural {S T : CommRingCat.{u}} (f : S ⟶ T)
    {M N : (Spec T).Modules} (g : M ⟶ N)
    (x : moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map f)).obj M)) :
    (PushforwardGlobalSections318.globalIso f N).hom
      ((moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (Spec.map f)).map g)) x)=
    (moduleSpecΓFunctor.map g) ((PushforwardGlobalSections318.globalIso f M).hom x) := by
  have h := (pushforwardCompModulesSpecToSheafIso f).hom.naturality g
  exact congrArg (fun k => k.hom.app (op ⊤) x) h
end ActualTwoDescentTildeStructureNormalization318
