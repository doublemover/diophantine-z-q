module
public import SchemeOpenPullbackPointsRebuild318
public section
noncomputable section
namespace SchemeCompatibleOpenUnionRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X : Scheme.{u}} (U : X.OpenCover) (V : ∀ i,(U.X i).Opens)
/-- Actual union of open chart images; no finite-index or inhabited-index
assumption is required. Empty local opens and empty schemes are included. -/
def locus : X.Opens := ⨆ i, ((V i).ι ≫ U.f i).opensRange
lemma chart_mem (i : U.I₀) (x : U.X i) (hx : x ∈ V i) : U.f i x ∈ locus U V :=
  TopologicalSpace.Opens.mem_iSup.mpr ⟨i,⟨⟨x,hx⟩,rfl⟩⟩
variable (W : U.I₀ → U.I₀ → Scheme.{u})
  (a : ∀ i j,W i j ⟶ U.X i) (b : ∀ i j,W i j ⟶ U.X j)
  (H : ∀ i j,IsPullback (a i j) (b i j) (U.f i) (U.f j))
  (hv : ∀ i j,a i j ⁻¹ᵁ V i=b i j ⁻¹ᵁ V j)
include H hv in
/-- Compatible opens glue with EXACT chart restrictions. Their full
pullback-overlap comparison, rather than an informal atlas, is consumed. -/
lemma preimage (i : U.I₀) : U.f i ⁻¹ᵁ locus U V=V i := by
  ext x
  constructor
  · intro hx
    obtain ⟨j,y,hy⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have he : U.f i x=U.f j (y:U.X j) := hy.symm
    obtain ⟨w,hw1,hw2⟩ := SchemeOpenPullbackPointsRebuild318.pair (H i j) x (y:U.X j) he
    have hb : w ∈ b i j ⁻¹ᵁ V j := by change b i j w ∈ V j;rw [hw2];exact y.property
    rw [←hv i j] at hb
    change a i j w ∈ V i at hb
    rwa [hw1] at hb
  · exact chart_mem U V i x
/-- Opens on the target are determined on every chart of the actual cover. -/
lemma unique (Z : X.Opens) (hZ : ∀ i,U.f i ⁻¹ᵁ Z=V i) : Z=locus U V := by
  ext x
  obtain ⟨i,y,rfl⟩ := U.exists_eq x
  have hi : (U.f i y ∈ Z) ↔ y ∈ V i := by
    change (y ∈ U.f i ⁻¹ᵁ Z) ↔ y ∈ V i
    rw [hZ]
  constructor
  · intro hx;exact chart_mem U V i y (hi.mp hx)
  · intro hx
    obtain ⟨j,z,hz⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hz' : U.f j (z:U.X j) ∈ Z := by
      change (z:U.X j) ∈ U.f j ⁻¹ᵁ Z
      rw [hZ];exact z.property
    exact hz ▸ hz'
end SchemeCompatibleOpenUnionRebuild318
