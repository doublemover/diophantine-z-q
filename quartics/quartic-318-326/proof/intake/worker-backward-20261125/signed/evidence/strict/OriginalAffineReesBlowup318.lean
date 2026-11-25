module
public import OriginalAffineReesGrading318
public section
noncomputable section

namespace OriginalAffineReesBlowup318

open AlgebraicGeometry CategoryTheory Polynomial HomogeneousLocalization
open OriginalAffineReesGrading318

universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- This is an actual scheme (relative Proj on this affine), not data for
a future map, or an affine algebra whose properness is assumed. -/
abbrev blowup := Proj (grade I)

@[expose] def projection : blowup I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (grade I) ≫ Spec.map (gradeZero I).toCommRingCatIso.hom

theorem proper (fg : I.FG) : IsProper (projection I) := by
  let : Algebra.FiniteType (grade I 0) (Rees I) := finiteType_of_fg I fg
  unfold projection
  infer_instance

/-- Actual Rees element aT. No claim that T itself belongs to this ring. -/
abbrev generator (a : R) (ha : a ∈ I) : Rees I :=
  (homogeneous I 1 a (by simpa only [pow_one] using ha)).val

theorem generator_grade (a : R) (ha : a ∈ I) :
    generator I a ha ∈ grade I 1 :=
  (homogeneous I 1 a (by simpa only [pow_one] using ha)).property

abbrev chart (a : R) (ha : a ∈ I) := Away (grade I) (generator I a ha)

@[expose] def chartMap (a : R) (ha : a ∈ I) :
    Spec (CommRingCat.of (chart I a ha)) ⟶ blowup I :=
  Proj.awayι (grade I) (generator I a ha) (generator_grade I a ha) (by decide)

abbrev chartScalars (a : R) (ha : a ∈ I) : R →+* chart I a ha :=
  (fromZeroRingHom (grade I) _).comp (gradeZero I).toRingHom

@[reassoc]
theorem chart_over (a : R) (ha : a ∈ I) :
    chartMap I a ha ≫ projection I =
      Spec.map (CommRingCat.ofHom (chartScalars I a ha)) := by
  rw [projection, ← Category.assoc, chartMap, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

/-- At one actual thick node of an affine piece, use its real maximal
ideal, not the coordinate equation as a global presentation. -/
abbrev nodeBlowup (x : PrimeSpectrum R) := blowup x.asIdeal

theorem node_proper [IsNoetherianRing R] (x : PrimeSpectrum R) :
    IsProper (projection x.asIdeal) := proper _ (IsNoetherian.noetherian _)

end OriginalAffineReesBlowup318

#print axioms OriginalAffineReesBlowup318.proper
#print axioms OriginalAffineReesBlowup318.chart_over
#print axioms OriginalAffineReesBlowup318.node_proper
