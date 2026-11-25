module
public import OriginalSameJActualDiagonalOpen318
public import OriginalSameJMovingDiagonalCentre318
public import OriginalSameJMovableAffineGraphChart318

@[expose] public section
noncomputable section

namespace OriginalSameJWholeMovingDiagonalCartier318

open AlgebraicGeometry Algebra CategoryTheory CategoryTheory.Limits TopologicalSpace
open OriginalSameJActualDiagonalOpen318 (affineProductOpen affineDiagonal product_is_open product_diagonal)
open OriginalSameJMovingDiagonalCentre318 (movingRead x vanishes actual_diagonal_selection)
open OriginalCyclicDivisorCartierAllOpenFrames318 (Chart)
open scoped TensorProduct Polynomial
universe u

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]
  [Algebra k[X] A] [IsScalarTower k k[X] A]
  [Algebra.EssFiniteType k[X] A] [Algebra.FormallyUnramified k[X] A]
variable {C : Scheme.{u}} (f : C ⟶ Spec (CommRingCat.of k))
  (j : Spec (CommRingCat.of A) ⟶ C) [IsOpenImmersion j]
  (hbase : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))

abbrev D := CommRingCat.of (A ⊗[k] A)

abbrev disc : (A ⊗[k] A) ⧸ Ideal.span (Set.singleton (x (k:=k) (A:=A))) :=
  Classical.choose (actual_diagonal_selection (k:=k) (A:=A))

theorem disc_idem : disc (k:=k) (A:=A) * disc = disc :=
  (Classical.choose_spec (actual_diagonal_selection (k:=k) (A:=A))).1

theorem disc_kernel :
    RingHom.ker (OriginalCyclicDivisorFieldFibreCartier318.fibreRead
      (movingRead (k:=k) (A:=A)).toRingHom (x (k:=k) (A:=A)) (vanishes (k:=k) (A:=A))) =
        Ideal.span (Set.singleton (disc (k:=k) (A:=A))) :=
  (Classical.choose_spec (actual_diagonal_selection (k:=k) (A:=A))).2

abbrev graphMap := (movingRead (k:=k) (A:=A)).toRingHom

theorem graph_surjective : Function.Surjective (graphMap (k:=k) (A:=A)) :=
  OriginalSameJExactEtaleDiagonalFactor318.diagonal_surjective (D:=k) (A:=A)

variable (hr : ∀ a : A ⊗[k] A, a * x (k:=k) (A:=A) = 0 → a = 0)

abbrev graphChart : Chart
    (OriginalSameJMovableAffineGraphChart318.point
      (𝟙 (Spec (D (k:=k) (A:=A)))) (graphMap (k:=k) (A:=A))) :=
  OriginalSameJMovableAffineGraphChart318.chart
    (𝟙 (Spec (D (k:=k) (A:=A)))) (graphMap (k:=k) (A:=A)) (x (k:=k) (A:=A))
    (vanishes (k:=k) (A:=A)) (disc (k:=k) (A:=A))
    (disc_kernel (k:=k) (A:=A)) (disc_idem (k:=k) (A:=A))
    (graph_surjective (k:=k) (A:=A)) hr

def affineChart : Chart (affineDiagonal k A) := by
  let Q := graphChart (k:=k) (A:=A) hr
  refine ⟨Q.A,Q.j,Q.open_j,Q.c,Q.z,?_,Q.regular⟩
  simpa only [OriginalSameJMovableAffineGraphChart318.point, Category.comp_id] using Q.square

/-- The principal equation on the actual product opens is now the
Cartier equation of the original global diagonal, not of an unrelated
affine copy of the curve. -/
def chart : Chart (pullback.diagonal f) := by
  let Q := affineChart (k:=k) (A:=A) hr
  let e := affineProductOpen k A f j hbase
  letI : IsOpenImmersion e := product_is_open k A f j hbase
  exact ⟨Q.A,Q.j ≫ e,IsOpenImmersion.comp _ _,Q.c,Q.z ≫ j,
    Q.square.paste_vert (product_diagonal k A f j hbase),Q.regular⟩

/-- Every point of the same open of C, not just its generic or a
retained section, has its full diagonal image in this regular chart. -/
theorem chart_meets (a : Spec (CommRingCat.of A)) :
    pullback.diagonal f (j a) ∈ (chart f j hbase hr).V.1 := by
  let Q := graphChart (k:=k) (A:=A) hr
  let e := affineProductOpen k A f j hbase
  have h := OriginalSameJMovableAffineGraphChart318.meets
    (𝟙 (Spec (D (k:=k) (A:=A)))) (graphMap (k:=k) (A:=A)) (x (k:=k) (A:=A))
    (vanishes (k:=k) (A:=A)) (disc (k:=k) (A:=A))
    (disc_kernel (k:=k) (A:=A)) (disc_idem (k:=k) (A:=A))
    (graph_surjective (k:=k) (A:=A)) hr a
  have ha : affineDiagonal k A a ∈ Q.V.1 := by
    simpa only [OriginalSameJMovableAffineGraphChart318.point,Category.comp_id] using h
  change affineDiagonal k A a ∈ Q.j ''ᵁ ⊤ at ha
  change pullback.diagonal f (j a) ∈ (Q.j ≫ e) ''ᵁ ⊤
  obtain ⟨v,hv,hav⟩ := ha
  refine ⟨v,hv,?_⟩
  have w := congrArg (fun m : Spec (CommRingCat.of A) ⟶ pullback f f => m a)
    (product_diagonal k A f j hbase).w
  calc
    (Q.j ≫ e) v = e (Q.j v) := Scheme.Hom.comp_apply Q.j e v
    _ = e (affineDiagonal k A a) := congrArg (fun q => e q) hav
    _ = pullback.diagonal f (j a) := by simpa only [Scheme.Hom.comp_apply] using w

end OriginalSameJWholeMovingDiagonalCartier318

#print axioms OriginalSameJWholeMovingDiagonalCartier318.disc_kernel
#print axioms OriginalSameJWholeMovingDiagonalCartier318.affineChart
#print axioms OriginalSameJWholeMovingDiagonalCartier318.chart
#print axioms OriginalSameJWholeMovingDiagonalCartier318.chart_meets
