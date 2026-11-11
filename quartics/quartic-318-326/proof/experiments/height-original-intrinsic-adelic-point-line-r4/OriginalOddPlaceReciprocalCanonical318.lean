module
public import OriginalEvenCanonicalExtension318
public import OriginalOddCanonicalFibers318
public section
noncomputable section
namespace OriginalOddPlaceReciprocalCanonical318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  (h2 : IsUnit (2:V c t w))
include h2 in
/-- At EVERY odd place where the actual original contact coordinate is
nonintegral, parity and the correct smooth reciprocal chart are produced.
Each branch includes genuine canonical tensor extensions of BOTH SAME
global sections and recovery of the entire original generic scheme point.
No contact-separation premise and no unit assumption on original twists
are imposed. Characteristic two and global Hodge/KS remain separate. -/
theorem exists_extension (ht : ¬w (t:K c t)≤1) :
    (∃ he : ∀ i,D.exponent i=0,Nonempty (OriginalEvenCanonicalExtension318.Extension c t w D he)) ∨
    (∃ ho : ∀ i,D.exponent i=1,Nonempty (OriginalCommonOddCanonicalExtension318.Extension c t w D ho)) := by
  rcases OriginalReciprocalParity318.even_or_odd c t w D ht with he|ho
  · exact Or.inl ⟨he,OriginalEvenCanonicalExtension318.exists_extension c t w D he h2 ht⟩
  · exact Or.inr ⟨ho,OriginalCommonOddCanonicalExtension318.exists_extension c t w D ho h2 ht⟩
end OriginalOddPlaceReciprocalCanonical318
