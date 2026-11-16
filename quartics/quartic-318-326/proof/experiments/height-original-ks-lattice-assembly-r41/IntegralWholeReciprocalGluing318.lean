module
public import IntegralWholeOrderOpenMaps318
public section
noncomputable section
namespace IntegralWholeReciprocalGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralWholeReciprocalOrders318 IntegralWholeOrderOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)
abbrev overlap : Scheme.{u} := Spec (CommRingCat.of (CommonOrder R c))
abbrev finiteScheme : Scheme.{u} := Spec (CommRingCat.of (FiniteOrder R c))
abbrev infinityScheme : Scheme.{u} := Spec (CommRingCat.of (InfinityOrder R c))
@[expose] def intoFinite : overlap R c ⟶ finiteScheme R c :=
  Spec.map (CommRingCat.ofHom (finiteMap R c))
@[expose] def intoInfinity : overlap R c ⟶ infinityScheme R c :=
  Spec.map (CommRingCat.ofHom (infinityMap R c))
instance intoFinite_open : IsOpenImmersion (intoFinite R c) := finiteMap_open R c
instance intoInfinity_open : IsOpenImmersion (intoInfinity R c) := infinityMap_open R c

/-- The actual full-chart projective-completion candidate. Both source
orders are finite free of rank8 over their polynomial coordinate bases;
the overlap retains every point whose coordinate is invertible. Properness
and comparison with the earlier restricted pushout are separate theorems. -/
abbrev scheme : Scheme.{u} := pushout (intoFinite R c) (intoInfinity R c)
@[expose] def finiteChart : finiteScheme R c ⟶ scheme R c := pushout.inl _ _
@[expose] def infinityChart : infinityScheme R c ⟶ scheme R c := pushout.inr _ _
instance finiteChart_open : IsOpenImmersion (finiteChart R c) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (intoFinite R c) (intoInfinity R c)) WalkingSpan.left))
instance infinityChart_open : IsOpenImmersion (infinityChart R c) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (intoFinite R c) (intoInfinity R c)) WalkingSpan.right))

theorem charts_cover (x : scheme R c) :
    (∃ a,finiteChart R c a=x) ∨ (∃ b,infinityChart R c b=x) := by
  obtain ⟨i,q,hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoFinite R c) (intoInfinity R c)) x
  cases i with
  | none =>
    left
    refine ⟨intoFinite R c q,?_⟩
    change ((intoFinite R c) ≫ finiteChart R c) q=x
    rw [show intoFinite R c ≫ finiteChart R c =
      colimit.ι (span (intoFinite R c) (intoInfinity R c)) WalkingSpan.zero from
      colimit.w (span (intoFinite R c) (intoInfinity R c)) WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q,hq⟩
    | right => exact Or.inr ⟨q,hq⟩

theorem intersection_square :
    IsPullback (intoFinite R c) (intoInfinity R c) (finiteChart R c) (infinityChart R c) :=
  GenericOpenPushout318.square _ _

/-- The exact original four-root affine source is an open chart in this
whole-order gluing, via the explicit coefficient-preserving equivalence. -/
@[expose] def originalSourceChart :
    Spec (CommRingCat.of (IntegralSourceBranches318.SourceOrder R c)) ⟶ scheme R c :=
  Spec.map (IntegralWholeFiniteComparison318.comparison R c).symm.toRingEquiv.toCommRingCatIso.hom ≫
    finiteChart R c
instance originalSourceChart_open : IsOpenImmersion (originalSourceChart R c) := by
  unfold originalSourceChart
  infer_instance
end IntegralWholeReciprocalGluing318
