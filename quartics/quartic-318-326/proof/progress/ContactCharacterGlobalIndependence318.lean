module
public import ContactCharacterFiniteIndependence318
public section
noncomputable section
namespace ContactCharacterGlobalIndependence318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open CharacterCoordinateDifferentials318
open scoped BigOperators
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-- Rational constants through the actual source structure morphism. -/
@[expose] def constants : ℚ→+*Γ(ContactGlobalSmooth318.Model units,⊤):=
  (ContactIntrinsicDifferentials318.structureMap units).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv.hom

theorem constants_restrict (a:ℚ):
    (ContactGlobalSmooth318.Model units).presheaf.map (homOfLE (show
      SourceGlobalAffine318.chartEmbedding units ''ᵁ ⊤ ≤ ⊤ from le_top)).op
        (constants a)=CharacterPullbackNormalization318.scalar (algebraMap ℚ S a):=by
  exact DFunLike.congr_fun (RingHom.ext_rat
    (((ContactGlobalSmooth318.Model units).presheaf.map (homOfLE (show
      SourceGlobalAffine318.chartEmbedding units ''ᵁ ⊤ ≤ ⊤ from le_top)).op).hom.comp constants)
    ((((SourceGlobalAffine318.chartEmbedding units).appIso ⊤).inv.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).comp (algebraMap ℚ S))) a

/-- The four globally pulled published elliptic invariant differentials are
Q-linearly independent in the actual intrinsic Omega of the complete source.
The scalar action is explicitly the one from its actual Q-structure map. -/
theorem global_linear_independent (a:Fin 4→ℚ)
    (h:∑i,constants (a i) • ContactCharacterDifferentials318.differential i=0):
    ∀i,a i=0:=by
  have e:=congrArg ((ContactIntrinsicDifferentials318.omega units).presheaf.map
    (homOfLE (show SourceGlobalAffine318.chartEmbedding units ''ᵁ ⊤ ≤ ⊤ from le_top)).op) h
  simp only [map_sum,Scheme.Modules.map_smul,map_zero,constants_restrict] at e
  apply ContactCharacterFiniteIndependence318.finite_linear_independent a
  apply (IntrinsicAffineSectionEquiv318.sectionMap_bijective
    (SourceGlobalAffine318.chartEmbedding units) (ContactIntrinsicDifferentials318.structureMap units)
      (SourceGlobalAffine318.chartEmbedding_over_Q units)).1
  simp only [map_sum,map_zero,IntrinsicChartSections318.section_smul,
    ContactCharacterAffinePullback318.finite_restrict]
  exact e
end ContactCharacterGlobalIndependence318
