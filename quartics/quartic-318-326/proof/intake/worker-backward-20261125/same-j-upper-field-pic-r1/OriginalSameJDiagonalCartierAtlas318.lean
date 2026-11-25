module
public import OriginalSameJWholeMovingDiagonalCartier318
public import OriginalSameJDiagonalCoordinateRegular318
public import OriginalCyclicDivisorRetainedCartierCover318

@[expose] public section
noncomputable section

namespace OriginalSameJDiagonalCartierAtlas318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalCyclicDivisorCartierAllOpenFrames318 (Chart)
open scoped Polynomial
universe u v

variable {k : Type u} [Field k]
variable {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of k))
variable [IsClosedImmersion (pullback.diagonal f)]
variable {ι : Type v} (A : ι → Type u)
variable [∀ i,CommRing (A i)] [∀ i,Algebra k (A i)] [∀ i,Algebra k[X] (A i)]
variable [∀ i,IsScalarTower k k[X] (A i)]
variable [∀ i,Algebra.EssFiniteType k[X] (A i)]
variable [∀ i,Algebra.FormallyUnramified k[X] (A i)]
variable [∀ i,Module.Flat k[X] (A i)]
variable (j : ∀ i,Spec (CommRingCat.of (A i)) ⟶ C) [∀ i,IsOpenImmersion (j i)]
variable (read : ∀ i,j i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (A i))))

/-- Full actual scheme coverage, including the complementary open
without any closed fibre of the diagonal: on it the equation is 1. -/
theorem cover
    (onC : ∀ x : C, ∃ i,∃ a : Spec (CommRingCat.of (A i)),j i a=x)
    (q : pullback f f) : ∃ Q : Chart (pullback.diagonal f),q ∈ Q.V.1 := by
  classical
  by_cases h : q ∈ Set.range (pullback.diagonal f)
  · obtain ⟨z,rfl⟩ := h
    obtain ⟨i,a,rfl⟩ := onC z
    let hr := OriginalSameJDiagonalCoordinateRegular318.regular (k:=k) (A:=A i)
    exact ⟨OriginalSameJWholeMovingDiagonalCartier318.chart f (j i) (read i) hr,
      OriginalSameJWholeMovingDiagonalCartier318.chart_meets f (j i) (read i) hr a⟩
  · exact OriginalCyclicDivisorRetainedCartierCover318.empty_at (pullback.diagonal f) h

end OriginalSameJDiagonalCartierAtlas318

#print axioms OriginalSameJDiagonalCartierAtlas318.cover
