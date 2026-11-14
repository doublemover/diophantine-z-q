module
public import AffineFrameRule318
public section
noncomputable section
namespace AffineFrameOverlapCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {X : Scheme.{u}} (U : X.AffineOpenCover) (i j : U.I₀)
abbrev overlap := pullback (U.f i) (U.f j)
abbrev cover : (overlap U i j).AffineOpenCover := (overlap U i j).affineOpenCover
abbrev left (k : (cover U i j).I₀) : Spec ((cover U i j).X k) ⟶ Spec (U.X i) :=
  (cover U i j).f k ≫ pullback.fst (U.f i) (U.f j)
abbrev right (k : (cover U i j).I₀) : Spec ((cover U i j).X k) ⟶ Spec (U.X j) :=
  (cover U i j).f k ≫ pullback.snd (U.f i) (U.f j)
abbrev into (k : (cover U i j).I₀) : Spec ((cover U i j).X k) ⟶ X := left U i j k ≫ U.f i
@[reassoc] lemma right_into (k : (cover U i j).I₀) : right U i j k ≫ U.f j=into U i j k := by
  simp only [right,into,left,Category.assoc,pullback.condition]
lemma image_le (k : (cover U i j).I₀) :
    into U i j k ''ᵁ ⊤≤(U.f i ''ᵁ ⊤) ⊓ (U.f j ''ᵁ ⊤) := by
  apply le_inf
  · exact OpenChartSections318.imageLE (left U i j k) (U.f i)
  · rw [←right_into]
    exact OpenChartSections318.imageLE (right U i j k) (U.f j)
/-- Every point of the FULL original overlap is covered by these actual
common affine tests. Nilpotents are retained by the original open schemes. -/
lemma covers : (U.f i ''ᵁ ⊤) ⊓ (U.f j ''ᵁ ⊤)≤⨆k,into U i j k ''ᵁ ⊤ := by
  intro x hx
  have hx' : x∈(pullback.fst (U.f i) (U.f j) ≫ U.f i) ''ᵁ ⊤ := by
    rw [OriginalFrameActualIntersections318.image (fun k => Spec (U.X k)) U.f i j]
    exact hx
  obtain ⟨y,_,hy⟩ := hx'
  obtain ⟨k,z,hz⟩ := (cover U i j).openCover.exists_eq y
  apply Opens.mem_iSup.mpr
  refine ⟨k,z,trivial,?_⟩
  change (U.f i) ((pullback.fst (U.f i) (U.f j)) ((cover U i j).f k z))=x
  rw [hz]
  exact hy
end AffineFrameOverlapCover318
