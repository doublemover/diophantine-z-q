module
public import ProperFiniteFiberDescent318
public section
noncomputable section
namespace ProperSelfRelationFinite318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

/-- Finiteness of the actual self-relation projection forces finite
fibers of the original map. Scheme pullbacks lift every equal-image pair,
including nonclosed points with unrelated residue fields. -/
lemma finite_of_self_pullback {X Y : Scheme} (f : X ⟶ Y) [IsProper f]
    [IsFinite (pullback.snd f f)] : IsFinite f := by
  letI : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f (by
    intro y
    by_cases hn : (f ⁻¹' {y}).Nonempty
    · obtain ⟨x,hx⟩ := hn
      change f x=y at hx
      have hs : f ⁻¹' {y} ⊆ pullback.fst f f '' ((pullback.snd f f) ⁻¹' {x}) := by
        intro z hz
        change f z=y at hz
        obtain ⟨w,hw,hv⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := f) z x
          (show f z=f x from hz.trans hx.symm)
        exact ⟨w,hv,hw⟩
      exact (((pullback.snd f f).finite_preimage_singleton x).image (pullback.fst f f)).subset hs
    · rw [Set.not_nonempty_iff_eq_empty] at hn
      rw [hn]
      exact Set.finite_empty)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f
end ProperSelfRelationFinite318
