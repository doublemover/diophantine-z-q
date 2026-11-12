module
public import CartierCanonicalSection318
public import AffineClosedRestrictionChart318
public section
noncomputable section
namespace CartierFramedAffineCover318
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {Z X : Scheme.{u}} (p : Z ⟶ X) [IsClosedImmersion p]
  (hp : OriginalRegularClosedCharts318.Property p)
local notation "L" => CartierCanonicalSection318.idealLine p hp
structure Index where
  frame : L.Index
  affine : X.affineOpens
  le_frame : affine.1≤L.opens frame
abbrev ring (i : Index p hp) : CommRingCat.{u} := Γ(X,i.affine.1)
@[expose] def into (i : Index p hp) : Spec (ring p hp i) ⟶ X := i.affine.2.fromSpec
instance (i : Index p hp) : IsOpenImmersion (into p hp i) := inferInstance
lemma image (i : Index p hp) : into p hp i ''ᵁ ⊤=i.affine.1 := by
  rw [Scheme.Hom.image_top_eq_opensRange]
  apply Opens.ext
  exact i.affine.2.range_fromSpec
lemma frame_le (i : Index p hp) : into p hp i ''ᵁ ⊤≤L.opens i.frame := by
  rw [image]
  exact i.le_frame
/-- All framed affine subopens cover the whole original scheme. -/
lemma cover : ⊤≤⨆i : Index p hp,(into p hp i).opensRange := by
  intro x _
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (L.cover (show x∈(⊤:X.Opens) from trivial))
  obtain ⟨V,hV,hx,hVi⟩ := exists_isAffineOpen_mem_and_subset hi
  let k : Index p hp := ⟨i,⟨V,hV⟩,hVi⟩
  apply (le_iSup (fun i : Index p hp => (into p hp i).opensRange) k)
  change x∈(into p hp k).opensRange
  rw [← Scheme.Hom.image_top_eq_opensRange,image]
  exact hx
end CartierFramedAffineCover318
