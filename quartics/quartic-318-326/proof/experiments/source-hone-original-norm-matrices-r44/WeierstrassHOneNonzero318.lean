module
public import WeierstrassOriginalResidue318
import all WeierstrassGluing318

public section
noncomputable section
namespace WeierstrassHOneNonzero318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open WeierstrassBoundaryClass318
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B : ℚ)

@[expose] def finiteSections : ShortAffineJacobian318.Ring A B ≃+
    Γ(Target A B,finiteOpen A B) :=
  AffineChartRingSections318.equivalenceOn (WeierstrassGluing318.finiteChart A B)
    (finiteOpen A B) (Scheme.Hom.image_top_eq_opensRange _)
@[expose] def infinitySections : InfinityChart318.Ring A B ≃+
    Γ(Target A B,infinityOpen A B) :=
  AffineChartRingSections318.equivalenceOn (WeierstrassGluing318.infinityChart A B)
    (infinityOpen A B) (Scheme.Hom.image_top_eq_opensRange _)

theorem restriction_on {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S]
    (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (f : R →+* S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))]
    (k : Spec (CommRingCat.of S) ⟶ X) [IsOpenImmersion k]
    (route : Spec.map (CommRingCat.ofHom f) ≫ j = k)
    (U V : X.Opens) (hU : j ''ᵁ ⊤ = U) (hV : k ''ᵁ ⊤ = V)
    (hVU : V ≤ U) (a : R) :
    X.presheaf.map (homOfLE hVU).op (AffineChartRingSections318.equivalenceOn j U hU a) =
      AffineChartRingSections318.equivalenceOn k V hV (f a) := by
  subst U
  exact AffineChartRingSections318.restrict_to_on j f k route V hV hVU a

theorem finite_restriction (a : ShortAffineJacobian318.Ring A B) :
    (Target A B).presheaf.map
      (homOfLE inf_le_left : finiteOpen A B ⊓ infinityOpen A B ⟶ finiteOpen A B).op
      (finiteSections A B a) =
        overlapSections A B (WeierstrassOverlap318.toInfinityBase A B a) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (WeierstrassOverlap318.toInfinityBase A B).toRingHom)) := by
    rw [← WeierstrassGluing318.intoAffine_eq]
    infer_instance
  apply restriction_on (WeierstrassGluing318.finiteChart A B)
    (WeierstrassOverlap318.toInfinityBase A B).toRingHom (overlapEmbedding A B)
    _ (finiteOpen A B) (finiteOpen A B ⊓ infinityOpen A B)
    (Scheme.Hom.image_top_eq_opensRange _) (overlap_image A B) inf_le_left a
  rw [← WeierstrassGluing318.intoAffine_eq]
  rfl

theorem infinity_restriction (a : InfinityChart318.Ring A B) :
    (Target A B).presheaf.map
      (homOfLE inf_le_right : finiteOpen A B ⊓ infinityOpen A B ⟶ infinityOpen A B).op
      (infinitySections A B a) =
        overlapSections A B (algebraMap (InfinityChart318.Ring A B) (Overlap A B) a) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (InfinityChart318.Ring A B) (Overlap A B)))) := by
    simpa only [WeierstrassGluing318.intoInfinity] using WeierstrassGluing318.intoInfinity_open A B
  apply restriction_on (WeierstrassGluing318.infinityChart A B)
    (algebraMap (InfinityChart318.Ring A B) (Overlap A B)) (overlapEmbedding A B)
    _ (infinityOpen A B) (finiteOpen A B ⊓ infinityOpen A B)
    (Scheme.Hom.image_top_eq_opensRange _) (overlap_image A B) inf_le_right a
  simpa only [WeierstrassGluing318.intoInfinity] using
    WeierstrassBoundaryClass318.overlap_infinity A B

/-- Uniform nonvanishing of the specified original structure-sheaf H1 class.
The proof uses both entire actual chart images, without a genus hypothesis. -/
theorem cohomologyClass_nonzero : cohomologyClass A B ≠ 0 := by
  intro h
  have hk := MayerVietorisSectionKernel318.sectionBoundary_kernel
    (StructureAdditiveSheaf318.sheaf (Target A B)) (finiteOpen A B) (infinityOpen A B)
    (cover A B) (overlapSections A B (representative A B))
  change cohomologyClass A B = 0 ↔
    ∃ (a : Γ(Target A B,finiteOpen A B)) (b : Γ(Target A B,infinityOpen A B)),
      (Target A B).presheaf.map
        (homOfLE inf_le_left : finiteOpen A B ⊓ infinityOpen A B ⟶ finiteOpen A B).op a -
      (Target A B).presheaf.map
        (homOfLE inf_le_right : finiteOpen A B ⊓ infinityOpen A B ⟶ infinityOpen A B).op b =
      overlapSections A B (representative A B) at hk
  obtain ⟨a,b,hab⟩ := hk.mp h
  obtain ⟨a,rfl⟩ := (finiteSections A B).surjective a
  obtain ⟨b,rfl⟩ := (infinitySections A B).surjective b
  rw [finite_restriction,infinity_restriction,← map_sub] at hab
  have he := (overlapSections A B).injective hab
  have hr := congrArg (WeierstrassOriginalResidue318.originalResidue A B) he
  rw [map_sub,WeierstrassOriginalResidue318.residue_finite,
    WeierstrassOriginalResidue318.residue_infinity,
    WeierstrassOriginalResidue318.residue_representative] at hr
  norm_num at hr

end WeierstrassHOneNonzero318
