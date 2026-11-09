module
public import AffineChartRingSections318
public import WeierstrassChartPullback318
public import MayerVietorisSectionKernel318
public import SheafCohomologyRetraction318

public section
noncomputable section
namespace WeierstrassBoundaryClass318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (A B : ℚ)
abbrev Target := WeierstrassGluing318.scheme A B
abbrev Overlap := WeierstrassOverlap318.InfinityOverlap A B
abbrev finiteOpen : (Target A B).Opens := (WeierstrassGluing318.finiteChart A B).opensRange
abbrev infinityOpen : (Target A B).Opens := (WeierstrassGluing318.infinityChart A B).opensRange

@[expose] def overlapEmbedding : Spec (CommRingCat.of (Overlap A B)) ⟶ Target A B :=
  WeierstrassGluing318.intoAffine A B ≫ WeierstrassGluing318.finiteChart A B
instance overlapOpen : IsOpenImmersion (overlapEmbedding A B) := by
  unfold overlapEmbedding
  infer_instance

theorem overlap_image : overlapEmbedding A B ''ᵁ ⊤ = finiteOpen A B ⊓ infinityOpen A B := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  ext x
  change (∃ z, overlapEmbedding A B z = x) ↔
    (∃ a, WeierstrassGluing318.finiteChart A B a = x) ∧
    (∃ b, WeierstrassGluing318.infinityChart A B b = x)
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨⟨WeierstrassGluing318.intoAffine A B z,rfl⟩,
      ⟨WeierstrassGluing318.intoInfinity A B z,?_⟩⟩
    exact congrArg (fun g => g z) (pushout.condition
      (f:=WeierstrassGluing318.intoAffine A B) (g:=WeierstrassGluing318.intoInfinity A B)).symm
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    obtain ⟨z,hza,hzb⟩ := WeierstrassChartPullback318.exists_overlap A B a b (ha.trans hb.symm)
    refine ⟨z,?_⟩
    change WeierstrassGluing318.finiteChart A B (WeierstrassGluing318.intoAffine A B z) = x
    rw [hza,ha]

theorem cover : finiteOpen A B ⊔ infinityOpen A B = ⊤ := by
  apply top_unique
  intro x hx
  rcases WeierstrassGluing318.charts_cover A B x with ha | hb
  · exact Or.inl ha
  · exact Or.inr hb

@[expose] def overlapSections : Overlap A B ≃+ Γ(Target A B,finiteOpen A B ⊓ infinityOpen A B) :=
  AffineChartRingSections318.equivalenceOn (overlapEmbedding A B)
    (finiteOpen A B ⊓ infinityOpen A B) (overlap_image A B)

/-- The literal overlap element x_aff²/y_aff, transported by the existing overlap isomorphism. -/
@[expose] def representative : Overlap A B :=
  (WeierstrassOverlap318.overlapEquiv A B).symm
    (WeierstrassOverlap318.ax A B ^ 2 * WeierstrassOverlap318.ai A B)

/-- A specified actual H1 class on the original completed scheme; nonvanishing is not assumed. -/
@[expose] def cohomologyClass : SheafCohomologyRetraction318.structureH (Target A B) 1 :=
  MayerVietorisSectionKernel318.sectionBoundary (StructureAdditiveSheaf318.sheaf (Target A B))
    (finiteOpen A B) (infinityOpen A B) (cover A B) (overlapSections A B (representative A B))

end WeierstrassBoundaryClass318
