module
public import IntegralOriginalInfinityEmbedding318
public section
noncomputable section
namespace IntegralOriginalChartsProperCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalGluing318
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem originalSource_range : (originalSourceChart R c).opensRange=(finiteChart R c).opensRange := by
  rw [originalSourceChart,Scheme.Hom.opensRange_comp_of_isIso]

/-- The original WHOLE finite source and the original RESTRICTED infinity
chart already cover the newly constructed proper model. All omitted infinity
branch points lie in the finite source by the full coordinate overlap. -/
theorem cover (x : scheme R c) :
    (∃ a,originalSourceChart R c a=x) ∨
    (∃ b,IntegralOriginalInfinityEmbedding318.chart R c b=x) := by
  obtain ⟨a,rfl⟩ | ⟨b,rfl⟩ := charts_cover R c x
  · left
    have h : finiteChart R c a ∈ (finiteChart R c).opensRange := ⟨a,rfl⟩
    rw [←originalSource_range] at h
    exact h
  · obtain hu | hd := infinity_opens_cover R c b
    · left
      rw [←IntegralWholeOpenRanges318.infinity_range R c] at hu
      obtain ⟨q,hq⟩ := hu
      have he : infinityChart R c b=finiteChart R c (intoFinite R c q) := by
        rw [←hq]
        exact congrArg (fun f => f q)
          (pushout.condition (f:=intoFinite R c) (g:=intoInfinity R c)).symm
      have h : infinityChart R c b ∈ (finiteChart R c).opensRange := ⟨intoFinite R c q,he.symm⟩
      rw [←originalSource_range] at h
      exact h
    · right
      rw [←IntegralOriginalInfinityEmbedding318.inclusion_range R c] at hd
      obtain ⟨q,hq⟩ := hd
      exact ⟨q,congrArg (infinityChart R c) hq⟩
end IntegralOriginalChartsProperCover318
