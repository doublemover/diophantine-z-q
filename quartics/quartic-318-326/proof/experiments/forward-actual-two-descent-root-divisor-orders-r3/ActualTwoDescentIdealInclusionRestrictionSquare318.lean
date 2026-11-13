module
public import ActualTwoDescentTildeStructureNormalization318
public section
noncomputable section
namespace ActualTwoDescentIdealInclusionRestrictionSquare318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentTildeStructureNormalization318
open ActualTwoDescentCanonicalIdealLocalizationMap318 ActualTwoDescentCanonicalIdealRestrictionComparison318
universe u
variable {R : Type u} [CommRing R]
def inclusion (I : Ideal R) : tilde (ModuleCat.of R I) ⟶
    SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf :=
  tilde.map (ModuleCat.ofHom I.subtype) ≫ tildeSelf.hom

lemma inclusion_global (I : Ideal R) (x : I) :
    (inclusion I).app ⊤ ((tilde.isoTop (ModuleCat.of R I)).hom x)=
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv (x:R) := by
  have h := (tilde.toTildeΓNatIso (R:=CommRingCat.of R)).hom.naturality (ModuleCat.ofHom I.subtype)
  have hx := congrArg (fun f => f x) h.symm
  change (tilde.map (ModuleCat.ofHom I.subtype)).app ⊤
    ((tilde.isoTop (ModuleCat.of R I)).hom x)=(tilde.isoTop (ModuleCat.of R R)).hom (x:R) at hx
  exact hx.trans (isoTop_ring (x:R))

variable (S : Type u) [CommRing S] [Algebra R S] (I : Ideal R)
/-- Whole pushed sheaf square: literal ideal localization respects the
ACTUAL structure-sheaf map and the literal ideal inclusions. -/
lemma pushed_inclusion_square :
    sheafMap S I ≫ (Scheme.Modules.pushforward (baseMap S)).map
      (inclusion (I.map (algebraMap R S)))=
    inclusion I ≫ StructurePushforwardSplit318.unitMap (baseMap S) := by
  apply tilde_hom_ext
  intro x
  apply (ConcreteCategory.bijective_of_isIso
    (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap R S))
      (SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf)).hom).injective
  change (PushforwardGlobalSections318.globalIso _ _).hom
    ((moduleSpecΓFunctor.map ((Scheme.Modules.pushforward (baseMap S)).map
      (inclusion (I.map (algebraMap R S)))))
      ((sheafMap S I).app ⊤ ((tilde.isoTop (ModuleCat.of R I)).hom x)))=_
  rw [pushforward_global_natural,global_image,inclusion_global]
  change _=(PushforwardGlobalSections318.globalIso _ _).hom
    ((moduleSpecΓFunctor.map (StructurePushforwardSplit318.unitMap (baseMap S)))
      ((inclusion I).app ⊤ ((tilde.isoTop (ModuleCat.of R I)).hom x)))
  rw [inclusion_global,structure_global]
  rfl

variable (M : Submonoid R) [IsLocalization M S] [IsOpenImmersion (baseMap S)]
/-- The exact canonical restriction comparison commutes with inclusion
into O on WHOLE sheaves,not merely on their fraction fields. -/
lemma restriction_inclusion_square :
    (restrictionIso S M I).hom ≫ inclusion (I.map (algebraMap R S))=
    (Scheme.Modules.restrictFunctor (baseMap S)).map (inclusion I) ≫
      (Scheme.Modules.restrictUnitIso (baseMap S)).hom := by
  apply ((Scheme.Modules.restrictAdjunction (baseMap S)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right,restriction_adjoint,
    Adjunction.homEquiv_naturality_left,restrictUnit_adjoint]
  exact pushed_inclusion_square S I
end ActualTwoDescentIdealInclusionRestrictionSquare318
