module
public import OriginalEvenFiniteCanonicalExtension318
public import OriginalOddPlaceReciprocalCanonical318
public section
noncomputable section
namespace OriginalSeparatedOddCanonical318
open NumberField FourRootPivot318 OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
variable (c : Fin 4 → ℚˣ) (tau : ℚ) (w : FinitePlace (K c tau)) (D : Data c tau w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c tau w
local notation "a" => IntegralSourceBranches318.contacts V
variable (h2 : IsUnit (2:V))
include h2 in
/-- Every original finite point at an odd separated place obtains an
actual smooth canonical extension. Parity and the suitable pivot are
both produced, not supplied as favorable geometric assumptions. -/
theorem finite_extension (ht : w (tau:K c tau)≤1)
    (hsep : ∀ i j : Fin 4,i≠j→IsUnit (a i-a j)) :
    (∃ he : ∀ k,D.exponent k=0,∃ i,Nonempty (OriginalEvenFiniteCanonicalExtension318.Extension c tau w D he i)) ∨
    (∃ i,∃ hi : D.exponent i=1,Nonempty (OriginalFinitePivotCanonicalExtension318.Extension c tau w D i hi)) := by
  classical
  by_cases ho : ∃ i,D.exponent i=1
  · obtain ⟨i,hi⟩ := ho
    have hs (j : Fin 3) : IsUnit (a i-a (indices i j.succ)) := by
      apply hsep
      intro h
      have hh : (0:Fin 4)=j.succ := (indices_injective i) ((indices_zero i).trans h)
      exact Fin.succ_ne_zero j hh.symm
    exact Or.inr ⟨i,hi,OriginalFinitePivotCanonicalExtension318.exists_extension c tau w D i hi h2 ht hs⟩
  · have he : ∀ k,D.exponent k=0 := by
      intro k
      rcases (show ∀ e : Fin 2,e=0 ∨ e=1 from by decide) (D.exponent k) with hk|hk
      · exact hk
      · exact False.elim (ho ⟨k,hk⟩)
    exact Or.inl ⟨he,OriginalEvenFiniteCanonicalExtension318.exists_extension c tau w D he h2 ht hsep⟩

include h2 in
/-- Complete original-point local canonical coverage at every odd place
where contacts remain separated. All four alternatives carry genuine
smooth integral charts, both SAME global canonical tensor extensions,
and entire original generic scheme-point recovery. No global Hodge or
relative-dualizing identification is inferred from this local cover. -/
theorem exists_extension (hsep : ∀ i j : Fin 4,i≠j→IsUnit (a i-a j)) :
    ((w (tau:K c tau)≤1) ∧
      ((∃ he : ∀ k,D.exponent k=0,∃ i,Nonempty (OriginalEvenFiniteCanonicalExtension318.Extension c tau w D he i)) ∨
       (∃ i,∃ hi : D.exponent i=1,Nonempty (OriginalFinitePivotCanonicalExtension318.Extension c tau w D i hi)))) ∨
    ((¬w (tau:K c tau)≤1) ∧
      ((∃ he : ∀ k,D.exponent k=0,Nonempty (OriginalEvenCanonicalExtension318.Extension c tau w D he)) ∨
       (∃ ho : ∀ k,D.exponent k=1,Nonempty (OriginalCommonOddCanonicalExtension318.Extension c tau w D ho)))) := by
  by_cases ht : w (tau:K c tau)≤1
  · exact Or.inl ⟨ht,finite_extension c tau w D h2 ht hsep⟩
  · exact Or.inr ⟨ht,OriginalOddPlaceReciprocalCanonical318.exists_extension c tau w D h2 ht⟩
end OriginalSeparatedOddCanonical318
