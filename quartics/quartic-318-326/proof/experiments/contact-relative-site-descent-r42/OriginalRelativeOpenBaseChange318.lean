module
public import ContactRelativeAffinePresieve318
public section
noncomputable section
namespace OriginalRelativeOpenBaseChange318
open AlgebraicGeometry CategoryTheory
open OriginalRelativeSite318
universe u
variable {X Y B : Scheme.{u}} (b : Y ⟶ B) (b' : X ⟶ B) (f : X ⟶ Y) (hf : f ≫ b = b')

include hf in
lemma base_square (U : Y.Opens) : (f ∣_ U) ≫ (U.ι ≫ b) = (f ⁻¹ᵁ U).ι ≫ b' := by
  rw [← Category.assoc,morphismRestrict_ι,Category.assoc,hf]

/-- The genuine base change of an original relative arrow to an open,
with its original inverse-image open and restriction morphism. -/
abbrev restrictedArrow (U : Y.Opens) : openObject b' (f ⁻¹ᵁ U) ⟶ openObject b U :=
  arrow (U.ι ≫ b) ((f ⁻¹ᵁ U).ι ≫ b') (f ∣_ U) (base_square b b' f hf U)

lemma square (U : Y.Opens) :
    restrictedArrow b b' f hf U ≫ openArrow b U = openArrow b' (f ⁻¹ᵁ U) ≫ arrow b b' f hf := by
  ext
  exact morphismRestrict_ι f U

lemma nested {U V : Y.Opens} (h : V ≤ U) :
    restrictedArrow b b' f hf V ≫ openInclusion b h =
      openInclusion b' (f.preimage_mono h) ≫ restrictedArrow b b' f hf U := by
  ext
  exact morphismRestrict_homOfLE f V U h

lemma affine_cover : (⊤ : Y.Opens) ≤ iSup (fun U : Y.affineOpens => U.1) := by
  rw [iSup_affineOpens_eq_top Y]

lemma inverse_image_cover {ι : Type u} (U : ι → Y.Opens) (hc : (⊤ : Y.Opens) ≤ iSup U) :
    (⊤ : X.Opens) ≤ iSup (fun i => f ⁻¹ᵁ U i) := by
  intro x hx
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hc (show f x ∈ (⊤ : Y.Opens) from trivial))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i,hi⟩
end OriginalRelativeOpenBaseChange318
