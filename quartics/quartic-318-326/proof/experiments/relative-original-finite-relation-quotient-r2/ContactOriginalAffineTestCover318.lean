module
public import OriginalAffineTestOpen318
public import ContactWholeInfinityScheme318
public import ContactBicanonicalDegree318
public import ContactIntrinsicDifferentials318
public section
noncomputable section
namespace ContactOriginalAffineTestCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ)
abbrev X := ContactGlobalSmooth318.Model c
abbrev p := ContactIntrinsicDifferentials318.structureMap c
abbrev finiteOpen : (X c).Opens := (SourceGlobalAffine318.chartEmbedding c).opensRange
abbrev infinityOpen : (X c).Opens := (ContactWholeInfinityScheme318.into c).opensRange

lemma finite_affine : IsAffineOpen (finiteOpen c) :=
  isAffineOpen_opensRange (SourceGlobalAffine318.chartEmbedding c)
lemma infinity_affine : IsAffineOpen (infinityOpen c) :=
  isAffineOpen_opensRange (ContactWholeInfinityScheme318.into c)

lemma original_cover : finiteOpen c ⊔ infinityOpen c = ⊤ := by
  rw [finiteOpen,infinityOpen,SourceGlobalAffine318.chartEmbedding_range,
    ContactWholeInfinityScheme318.into_range]
  change ContactProjectiveModel318.modelMap c ⁻¹ᵁ (JLineAtlas318.chart ℚ 1 ''ᵁ ⊤) ⊔
    ContactProjectiveModel318.modelMap c ⁻¹ᵁ (JLineAtlas318.chart ℚ 0 ''ᵁ ⊤) = ⊤
  have h := ContactGlobalProper318.targetCover_covers
  simp only [ContactGlobalProper318.targetCover,Fin.iSup_univ_two] at h
  rw [← Scheme.Hom.preimage_sup,sup_comm,h,Scheme.Hom.preimage_top]

variable {T : Scheme.{0}} [IsAffine T] (b : T ⟶ Spec (CommRingCat.of ℚ))
/-- The unchanged full original relative-test curve, with p FIRST. -/
abbrev family := pullback (p c) b
abbrev finiteTest : (family c b).Opens := (pullback.fst (p c) b) ⁻¹ᵁ finiteOpen c
abbrev infinityTest : (family c b).Opens := (pullback.fst (p c) b) ⁻¹ᵁ infinityOpen c

lemma finiteTest_affine : IsAffineOpen (finiteTest c b) :=
  OriginalAffineTestOpen318.affine (p c) b (finiteOpen c) (finite_affine c)
lemma infinityTest_affine : IsAffineOpen (infinityTest c b) :=
  OriginalAffineTestOpen318.affine (p c) b (infinityOpen c) (infinity_affine c)
lemma test_cover : finiteTest c b ⊔ infinityTest c b = ⊤ :=
  OriginalAffineTestOpen318.cover (p c) b (finiteOpen c) (infinityOpen c) (original_cover c)
end ContactOriginalAffineTestCover318
