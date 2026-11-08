module
public import IntrinsicChartSections318
public section
noncomputable section
namespace IntrinsicAffineSectionEquiv318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {Y:Scheme.{u}} {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j:Spec (CommRingCat.of S)⟶Y) [IsOpenImmersion j]
    (p:Y⟶Spec (CommRingCat.of R))
    (h:j≫p=Spec.map (CommRingCat.ofHom (algebraMap R S)))

theorem sectionMap_bijective : Function.Bijective (IntrinsicChartSections318.sectionMap j p h) :=
  (ConcreteCategory.bijective_of_isIso
    (moduleSpecΓFunctor.map (IntrinsicChartNormalization318.iso j p h).hom)).comp
      (ConcreteCategory.bijective_of_isIso
        (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom)

/-- Every actual intrinsic section on the entire affine chart has a unique
ordinary algebraic differential, through the previously normalized chart iso. -/
@[expose] def equivalence : KaehlerDifferential R S ≃+
    Γ(FamilyIntrinsicDifferentials318.omega p,j ''ᵁ ⊤) :=
  AddEquiv.ofBijective (IntrinsicChartSections318.sectionMap j p h) (sectionMap_bijective j p h)

theorem apply_eq (ω:KaehlerDifferential R S) :
    equivalence j p h ω=IntrinsicChartSections318.sectionMap j p h ω := rfl
end IntrinsicAffineSectionEquiv318
