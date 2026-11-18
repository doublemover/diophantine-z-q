module
public import IntegralFourRootOverlap318
public import GenericOpenPushout318
public section
noncomputable section
namespace IntegralFourRootGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralFourRootReciprocalCharts318 IntegralFourRootOverlap318
universe u
variable (R : Type u) [CommRing R] (d a : Fin 4 → R)

abbrev overlap : Scheme.{u} := Spec (CommRingCat.of (CommonOrder R d a))
abbrev finiteScheme : Scheme.{u} := Spec (CommRingCat.of (FiniteOrder d a))
abbrev infinityScheme : Scheme.{u} := Spec (CommRingCat.of (ReciprocalOrder d a))
@[expose] def intoFinite : overlap R d a ⟶ finiteScheme R d a :=
  Spec.map (CommRingCat.ofHom (finiteMap R d a))
@[expose] def intoInfinity : overlap R d a ⟶ infinityScheme R d a :=
  Spec.map (CommRingCat.ofHom (infinityMap R d a))
instance intoFinite_open : IsOpenImmersion (intoFinite R d a) := finiteMap_open R d a
instance intoInfinity_open : IsOpenImmersion (intoInfinity R d a) := infinityMap_open R d a

/-- The two actual whole integral charts glued along their coordinate
localizations. Neither the twists nor residue characteristics are inverted.
This construction by itself does not assert normality or properness. -/
abbrev scheme : Scheme.{u} := pushout (intoFinite R d a) (intoInfinity R d a)
@[expose] def finiteChart : finiteScheme R d a ⟶ scheme R d a := pushout.inl _ _
@[expose] def infinityChart : infinityScheme R d a ⟶ scheme R d a := pushout.inr _ _
instance finiteChart_open : IsOpenImmersion (finiteChart R d a) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (intoFinite R d a) (intoInfinity R d a)) WalkingSpan.left))
instance infinityChart_open : IsOpenImmersion (infinityChart R d a) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (intoFinite R d a) (intoInfinity R d a)) WalkingSpan.right))

theorem charts_cover (x : scheme R d a) :
    (∃ p, finiteChart R d a p=x) ∨ (∃ q, infinityChart R d a q=x) := by
  obtain ⟨i,q,hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoFinite R d a) (intoInfinity R d a)) x
  cases i with
  | none =>
    left
    refine ⟨intoFinite R d a q,?_⟩
    change ((intoFinite R d a) ≫ finiteChart R d a) q=x
    rw [show intoFinite R d a ≫ finiteChart R d a =
      colimit.ι (span (intoFinite R d a) (intoInfinity R d a)) WalkingSpan.zero from
      colimit.w (span (intoFinite R d a) (intoInfinity R d a)) WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q,hq⟩
    | right => exact Or.inr ⟨q,hq⟩

theorem intersection_square : IsPullback (intoFinite R d a) (intoInfinity R d a)
    (finiteChart R d a) (infinityChart R d a) := GenericOpenPushout318.square _ _

end IntegralFourRootGluing318
