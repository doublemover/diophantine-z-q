module
public import NormalizedWholeOpenMaps318
public section
noncomputable section
namespace NormalizedWholeGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NormalizedWholeOverlap318 NormalizedWholeOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (d contacts : Fin 4 → R)
abbrev overlap : Scheme.{u} := Spec (CommRingCat.of (CommonOrder R d contacts))
abbrev finiteScheme : Scheme.{u} := Spec (CommRingCat.of (FiniteOrder R d contacts))
abbrev infinityScheme : Scheme.{u} := Spec (CommRingCat.of (InfinityOrder R d contacts))
@[expose] def intoFinite : overlap R d contacts ⟶ finiteScheme R d contacts :=
  Spec.map (CommRingCat.ofHom (finiteMap R d contacts))
@[expose] def intoInfinity : overlap R d contacts ⟶ infinityScheme R d contacts :=
  Spec.map (CommRingCat.ofHom (infinityMap R d contacts))
instance intoFinite_open : IsOpenImmersion (intoFinite R d contacts) := finiteMap_open R d contacts
instance intoInfinity_open : IsOpenImmersion (intoInfinity R d contacts) := infinityMap_open R d contacts

/-- The actual full-chart projective-completion candidate. Both source
orders are finite free of rank16 over their polynomial coordinate bases;
the overlap retains every point whose coordinate is invertible. Properness
and identification with the original rational normalization are separate theorems. -/
abbrev scheme : Scheme.{u} := pushout (intoFinite R d contacts) (intoInfinity R d contacts)
@[expose] def finiteChart : finiteScheme R d contacts ⟶ scheme R d contacts := pushout.inl _ _
@[expose] def infinityChart : infinityScheme R d contacts ⟶ scheme R d contacts := pushout.inr _ _
instance finiteChart_open : IsOpenImmersion (finiteChart R d contacts) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (intoFinite R d contacts) (intoInfinity R d contacts)) WalkingSpan.left))
instance infinityChart_open : IsOpenImmersion (infinityChart R d contacts) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (intoFinite R d contacts) (intoInfinity R d contacts)) WalkingSpan.right))

theorem charts_cover (x : scheme R d contacts) :
    (∃ a,finiteChart R d contacts a=x) ∨ (∃ b,infinityChart R d contacts b=x) := by
  obtain ⟨i,q,hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoFinite R d contacts) (intoInfinity R d contacts)) x
  cases i with
  | none =>
    left
    refine ⟨intoFinite R d contacts q,?_⟩
    change ((intoFinite R d contacts) ≫ finiteChart R d contacts) q=x
    rw [show intoFinite R d contacts ≫ finiteChart R d contacts =
      colimit.ι (span (intoFinite R d contacts) (intoInfinity R d contacts)) WalkingSpan.zero from
      colimit.w (span (intoFinite R d contacts) (intoInfinity R d contacts)) WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q,hq⟩
    | right => exact Or.inr ⟨q,hq⟩

theorem intersection_square :
    IsPullback (intoFinite R d contacts) (intoInfinity R d contacts) (finiteChart R d contacts) (infinityChart R d contacts) :=
  GenericOpenPushout318.square _ _

end NormalizedWholeGluing318
