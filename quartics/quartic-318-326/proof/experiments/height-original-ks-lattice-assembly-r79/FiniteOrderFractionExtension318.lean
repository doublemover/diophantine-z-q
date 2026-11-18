module
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Finiteness.Defs
public section
noncomputable section
namespace FiniteOrderFractionExtension318

/-- A finite order spanning its fraction field also spans it over any
compatible coefficient field. The coefficient action is the supplied tower,
not a finite/reciprocal parameter identification. -/
theorem finite (R B K L : Type*) [CommRing R] [IsDomain R]
    [CommRing B] [IsDomain B] [Field K] [Field L]
    [Algebra R B] [Algebra R K] [Algebra R L] [Algebra B L] [Algebra K L]
    [IsScalarTower R B L] [IsScalarTower R K L]
    [Module.Finite R B] [IsFractionRing B L]
    (hinj : Function.Injective (algebraMap R L)) : Module.Finite K L := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  refine Module.Finite.of_fg_top ⟨s.image (algebraMap B L), ?_⟩
  apply top_unique
  intro x hx
  have hspan : (Ideal.span ({1} : Set B) : Set B) ⊆ Submodule.span R (s : Set B) := by
    rw [hs]
    exact Set.subset_univ _
  have h := IsFractionRing.ideal_span_singleton_map_subset
    (R := R) (S := B) (K := K) (L := L) hinj hspan
  have hx' : x ∈ (Ideal.span ({algebraMap B L 1} : Set L) : Set L) := by
    simp
  have hmem := h hx'
  change x ∈ (Submodule.span K (↑(s.image (algebraMap B L)) : Set L) : Set L)
  simpa only [Finset.coe_image] using hmem

end FiniteOrderFractionExtension318
