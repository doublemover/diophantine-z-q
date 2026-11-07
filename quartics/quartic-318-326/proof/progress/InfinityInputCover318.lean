module
public import InfinityInputOverlapScheme318
public section
noncomputable section
namespace InfinityInputCover318
open InfinityInputAlgebra318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

/-- An explicit Bezout identity covers the entire mixed input product, over every base ring. -/
theorem bezout (A B:R) :
    (1+x A B*u A B^2)*denominator A B+
      v A B*(x A B^2*u A B*parameter A B+
        (1+x A B*u A B^2)*(coeff A B A*u A B+coeff A B B*v A B))=1 := by
  have hh:=left_relation A B
  unfold denominator InfinityInputPolynomial318.denominator parameter
  linear_combination (x A B^2*u A B)*hh

@[expose] def chartElement (A B:R) : Fin 2 → PairRing A B := ![v A B,denominator A B]

/-- The finite-first and regular infinity-input chart functions generate the unit ideal. -/
theorem chart_span_top (A B:R) : Ideal.span (Set.range (chartElement A B))=⊤ := by
  let I:=Ideal.span (Set.range (chartElement A B))
  have hv:v A B∈I:=Ideal.subset_span ⟨0,rfl⟩
  have hh:denominator A B∈I:=Ideal.subset_span ⟨1,rfl⟩
  apply (Ideal.eq_top_iff_one _).mpr
  rw [←bezout A B]
  apply I.add_mem (I.mul_mem_left _ hh)
  have hc:=I.mul_mem_left (x A B^2*u A B*parameter A B+
      (1+x A B*u A B^2)*(coeff A B A*u A B+coeff A B B*v A B)) hv
  convert hc using 1 <;> ring

/-- Actual two-open cover of the entire mixed tensor coordinate scheme. -/
@[expose] def coordinateCover (A B:R) : (Spec (CommRingCat.of (PairRing A B))).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R:=CommRingCat.of (PairRing A B))
    (chartElement A B) (chart_span_top A B)).openCover

/-- The actual infinity-chart times finite-chart fiber product is entirely covered. -/
@[expose] def productCover (A B:R) : (InfinityInputScheme318.productScheme A B).OpenCover :=
  (coordinateCover A B).pushforwardIso
    (pullbackSpecIso R (InfinityChart318.Ring A B) (ShortAffineJacobian318.Ring A B)).inv

@[simp] theorem productCover_infinityInput (A B:R) :
    (productCover A B).f (1:Fin 2)=InfinityInputScheme318.intoProduct A B := rfl

end InfinityInputCover318
