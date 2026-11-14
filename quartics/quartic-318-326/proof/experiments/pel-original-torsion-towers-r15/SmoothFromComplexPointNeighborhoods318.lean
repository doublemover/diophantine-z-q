module
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public section
noncomputable section
namespace SmoothFromComplexPointNeighborhoods318
open AlgebraicGeometry CategoryTheory Set
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] [LocallyOfFinitePresentation f]

/-- Smooth neighborhoods of ALL actual algebraically closed valued
points cover the entire finite-type scheme: a nonempty closed singular
locus would contain a closed point. No assertion that every scheme
point is itself a K-valued closed point is used. -/
theorem smooth
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ →
      ∃ U : Scheme.{u}, ∃ i : U ⟶ X, IsOpenImmersion i ∧ Smooth (i ≫ f) ∧
        ∃ q : Spec (CommRingCat.of K) ⟶ U, q ≫ i = p) :
    Smooth f := by
  letI := LocallyOfFiniteType.jacobsonSpace f
  rw [←Scheme.Hom.smoothLocus_eq_top_iff,←TopologicalSpace.Opens.coe_eq_univ,
    ←not_ne_iff,←Set.nonempty_compl]
  intro H
  obtain ⟨x,hx,hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  let p := pointOfClosedPoint f x hxc
  obtain ⟨U,i,hi,hs,q,hq⟩ := h p (pointOfClosedPoint_comp f x hxc)
  letI : IsOpenImmersion i := hi
  letI : Smooth (i ≫ f) := hs
  let o := IsLocalRing.closedPoint K
  have hmem : q o ∈ (i ≫ f).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  rw [←Scheme.Hom.preimage_smoothLocus_eq,Scheme.Hom.mem_preimage] at hmem
  have he : i (q o) = x := by
    calc
      i (q o) = p o := congrArg (fun l : Spec (CommRingCat.of K) ⟶ X => l o) hq
      _ = x := pointOfClosedPoint_apply f x hxc o
  exact hx (he ▸ hmem)
end SmoothFromComplexPointNeighborhoods318
