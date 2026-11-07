module
public import InfinityRelativeDimension318
import all WeierstrassGluing318
public section
noncomputable section
namespace GluedRelativeDimension318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassGluing318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R]

/-- The genuine glued two-chart curve is smooth of relative dimension one. -/
theorem structure_dimension_one (A B : R) (h2 : IsUnit (2:R))
    (hD : IsUnit (-16*(4*A^3+27*B^2))) :
    SmoothOfRelativeDimension 1 (structureMap A B) := by
  letI := AffineRelativeDimension318.structure_dimension_one A B hD
  letI := InfinityRelativeDimension318.structure_dimension_one A B h2
  apply IsZariskiLocalAtSource.of_openCover
    (Scheme.IsLocallyDirected.openCover (span (intoAffine A B) (intoInfinity A B)))
  intro i
  cases i with
  | none =>
    change SmoothOfRelativeDimension 1
      (colimit.ι (span (intoAffine A B) (intoInfinity A B)) WalkingSpan.zero ≫ structureMap A B)
    rw [←colimit.w (span (intoAffine A B) (intoInfinity A B)) WalkingSpan.Hom.fst]
    rw [Category.assoc]
    change SmoothOfRelativeDimension 1 (intoAffine A B ≫ finiteChart A B ≫ structureMap A B)
    rw [finiteChart_structure]
    exact inferInstanceAs (SmoothOfRelativeDimension (0+1)
      (intoAffine A B ≫ ShortAffineScheme318.structureMap A B))
  | some j =>
    cases j with
    | left =>
      change SmoothOfRelativeDimension 1 (finiteChart A B ≫ structureMap A B)
      rw [finiteChart_structure]
      infer_instance
    | right =>
      change SmoothOfRelativeDimension 1 (infinityChart A B ≫ structureMap A B)
      rw [infinityChart_structure]
      infer_instance

/-- Unconditional relative dimension one for the actual literal family over the open j-line. -/
instance literal_dimension_one (N : ℕ) : SmoothOfRelativeDimension 1 (literalStructureMap N) :=
  structure_dimension_one _ _ (OpenJModel318.base_units N).1
    (OpenJAffineScheme318.discriminant_unit N)

end GluedRelativeDimension318
