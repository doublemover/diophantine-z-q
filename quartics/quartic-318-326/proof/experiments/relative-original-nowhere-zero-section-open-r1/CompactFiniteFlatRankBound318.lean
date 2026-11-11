module
public import ContactBoundedCartierAbelNaturality318
public import Mathlib.Topology.LocallyConstant.Basic
public section
noncomputable section
namespace CompactFiniteFlatRankBound318
open AlgebraicGeometry
universe u
variable {Z B : Scheme.{u}} (p : Z ⟶ B)
  [hfinite : IsFinite p] [hflat : Flat p] [hpresentation : LocallyOfFinitePresentation p]
  [hcompact : CompactSpace B]
include hfinite hflat hpresentation hcompact in
/-- A genuine finite-flat finitely presented family over a quasi-compact
coefficient scheme has an internally produced finite rank bound. No
constant-rank or connectedness assumption is inserted. -/
lemma exists_bound : ∃ N : ℕ,∀ x : B,p.finrank x≤N := by
  have hf : (Set.range p.finrank).Finite := p.isLocallyConstant_finrank.range_finite
  obtain ⟨N,hN⟩ := hf.bddAbove
  exact ⟨N,fun x => hN ⟨x,rfl⟩⟩
@[expose] def bound : ℕ := Classical.choose (exists_bound p)
lemma rank_bound (x : B) : p.finrank x≤bound p := Classical.choose_spec (exists_bound p) x
end CompactFiniteFlatRankBound318
