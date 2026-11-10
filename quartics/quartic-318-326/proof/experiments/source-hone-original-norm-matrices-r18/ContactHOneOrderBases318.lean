module
public import RootOrderMonomialBasis318
public import SourceOpenFractionField318
public import InfinityOrderCoordinates318

public section
noncomputable section
namespace ContactHOneOrderBases318
open RootOrderMonomialBasis318 Polynomial
open scoped BigOperators
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)

/-- Original finite-chart coordinates over the original polynomial base. -/
@[expose] def finiteBasis : Module.Basis FourIndex ℚ[X] (ContactKummerOrder318.SourceOrder c) :=
  fourBasis (ContactKummerOrder318.coefficient c)

/-- Original overlap coordinates over the original localized polynomial base. -/
@[expose] def overlapBasis : Module.Basis FourIndex ContactKummerOrder318.OpenBase
    (ContactKummerOrder318.OpenOrder c) :=
  fourBasis (fun i => algebraMap ℚ[X] ContactKummerOrder318.OpenBase
    (ContactKummerOrder318.coefficient c i))

/-- Original infinity-chart coordinates over its original localized u-polynomial base. -/
@[expose] def infinityBasis : Module.Basis ThreeIndex (InfinityOpenChart318.OpenBase c)
    (InfinityOpenChart318.OpenOrder c) :=
  threeBasis (InfinityOrderCoordinates318.coefficient c)

/-- The actual finite-to-overlap map preserves each named monomial exactly. -/
theorem finite_to_overlap (i : FourIndex) :
    SourceOpenFractionField318.orderToOpen c (finiteBasis c i) = overlapBasis c i :=
  four_coefficientMap ContactKummerOrder318.OpenBase (ContactKummerOrder318.coefficient c) i

/-- Every original finite-ring element has its exact sixteen coefficient expansion. -/
theorem finite_expansion (x : ContactKummerOrder318.SourceOrder c) :
    ∑ i, (finiteBasis c).repr x i • finiteBasis c i = x := (finiteBasis c).sum_repr x

theorem overlap_expansion (x : ContactKummerOrder318.OpenOrder c) :
    ∑ i, (overlapBasis c).repr x i • overlapBasis c i = x := (overlapBasis c).sum_repr x

theorem infinity_expansion (x : InfinityOpenChart318.OpenOrder c) :
    ∑ i, (infinityBasis c).repr x i • infinityBasis c i = x := (infinityBasis c).sum_repr x

local instance originalField : Field (InfinityFieldCoordinates318.L c) :=
  (KummerTensorField318.source_raw_field c).toField

/-- Each actual infinity basis vector is the original product of root ratios
in the original contact field, with coefficient exactly one. -/
theorem infinity_embedding (i : ThreeIndex) :
    InfinityOpenFractionField318.openEmbedding c (infinityBasis c i) =
      InfinityFieldCoordinates318.ratio c 0 ^ (i.1 : ℕ) *
      InfinityFieldCoordinates318.ratio c 1 ^ (i.2.1 : ℕ) *
      InfinityFieldCoordinates318.ratio c 2 ^ (i.2.2 : ℕ) := by
  change InfinityOpenFractionField318.openEmbedding c
    (threeBasis (InfinityOrderCoordinates318.coefficient c) i) = _
  rw [threeBasis_monomial]
  simp only [map_mul, map_pow]
  change InfinityOpenFractionField318.openEmbedding c (InfinityOrderCoordinates318.generator c 0) ^ _ *
      InfinityOpenFractionField318.openEmbedding c (InfinityOrderCoordinates318.generator c 1) ^ _ *
      InfinityOpenFractionField318.openEmbedding c (InfinityOrderCoordinates318.generator c 2) ^ _ = _
  rw [InfinityOrderCoordinates318.generator_embedding,
    InfinityOrderCoordinates318.generator_embedding,InfinityOrderCoordinates318.generator_embedding]

end ContactHOneOrderBases318
