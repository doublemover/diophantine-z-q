module
public import IntrinsicChartNaturality318
public section
noncomputable section
namespace IntrinsicOverlapSections318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {Y : Scheme.{u}} {R S T C : Type u}
    [CommRing R] [CommRing S] [CommRing T] [CommRing C]
    [Algebra R S] [Algebra R T] [Algebra R C]
    (f : S →ₐ[R] C) (g : T →ₐ[R] C)
    (hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)))
    (hg : IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom)))
    (jS : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion jS]
    (jT : Spec (CommRingCat.of T) ⟶ Y) [IsOpenImmersion jT]
    (jC : Spec (CommRingCat.of C) ⟶ Y) [IsOpenImmersion jC]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (hS : jS ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (hT : jT ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R T)))
    (hC : jC ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R C)))
    (routeS : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ jS=jC)
    (routeT : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ jT=jC)
    (ωS : KaehlerDifferential R S) (ωT : KaehlerDifferential R T)
    (hω : AlgHomDifferential318.map f ωS=AlgHomDifferential318.map g ωT)

include hf hg hC routeS routeT hω

theorem common_agreement (hCS : jC ''ᵁ ⊤ ≤ jS ''ᵁ ⊤) (hCT : jC ''ᵁ ⊤ ≤ jT ''ᵁ ⊤) :
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hCS).op
      (IntrinsicChartSections318.sectionMap jS p hS ωS) =
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hCT).op
      (IntrinsicChartSections318.sectionMap jT p hT ωT) := by
  letI := hf
  letI := hg
  exact (IntrinsicChartNaturality318.section_restrict_to f jS p hS jC hC routeS hCS ωS).trans
    ((congrArg (IntrinsicChartSections318.sectionMap jC p hC) hω).trans
      (IntrinsicChartNaturality318.section_restrict_to g jT p hT jC hC routeT hCT ωT).symm)

/-- Agreement of algebraic invariant forms on a full actual common chart gives
literal compatibility of their intrinsic ambient sections on the full open
intersection. No dense-open replacement or presumed intrinsic descent occurs. -/
theorem intersection_agreement (himage : jC ''ᵁ ⊤ = (jS ''ᵁ ⊤) ⊓ (jT ''ᵁ ⊤)) :
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map
      (homOfLE (show (jS ''ᵁ ⊤) ⊓ (jT ''ᵁ ⊤) ≤ jS ''ᵁ ⊤ from inf_le_left)).op
      (IntrinsicChartSections318.sectionMap jS p hS ωS) =
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map
      (homOfLE (show (jS ''ᵁ ⊤) ⊓ (jT ''ᵁ ⊤) ≤ jT ''ᵁ ⊤ from inf_le_right)).op
      (IntrinsicChartSections318.sectionMap jT p hT ωT) := by
  let P (V : Y.Opens) := ∀ (hVS : V ≤ jS ''ᵁ ⊤) (hVT : V ≤ jT ''ᵁ ⊤),
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hVS).op
      (IntrinsicChartSections318.sectionMap jS p hS ωS) =
    (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hVT).op
      (IntrinsicChartSections318.sectionMap jT p hT ωT)
  have hc : P (jC ''ᵁ ⊤) := common_agreement f g hf hg jS jT jC p hS hT hC routeS routeT ωS ωT hω
  exact (Eq.mp (congrArg P himage) hc) inf_le_left inf_le_right
end IntrinsicOverlapSections318
