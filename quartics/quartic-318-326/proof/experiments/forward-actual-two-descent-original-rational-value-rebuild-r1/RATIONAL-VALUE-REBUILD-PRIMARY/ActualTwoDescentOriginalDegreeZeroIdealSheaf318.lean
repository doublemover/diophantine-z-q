module
public import ActualTwoDescentOriginalInverseInfinityTransition318
public section
noncomputable section
namespace ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ActualTwoDescentOriginalRootAffineSheaf318 ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentOriginalInverseInfinityTransition318
variable {K : Type*} [Field K] [CharZero K]

def affineIdealPushed (n : K) (i : Fin 3) : (originalCubicScheme n).Modules :=
  (Scheme.Modules.pushforward (affineChart n)).obj (rootAffineSheaf n i)
def infinityInversePushed (n : K) : (originalCubicScheme n).Modules :=
  (Scheme.Modules.pushforward (infinityChart n)).obj (ClutchedModule318.unit (infinityScheme n))
def overlapFunctionsPushed (n : K) : (originalCubicScheme n).Modules :=
  (Scheme.Modules.pushforward (intoAffine n ≫ affineChart n)).obj
    (ClutchedModule318.unit (overlapScheme n))

def affineIdealRestriction (n : K) (i : Fin 3) :
    affineIdealPushed n i ⟶ overlapFunctionsPushed n :=
  (Scheme.Modules.pushforward (affineChart n)).map (rootAffineInclusion n i) ≫
    ClutchedModule318.restriction (affineChart n) (intoAffine n)
lemma actual_original_overlap_square (n : K) :
    intoInfinity n ≫ infinityChart n=intoAffine n ≫ affineChart n :=
  (pushout.condition (intoAffine n) (intoInfinity n)).symm

/-- Infinity coefficients represent b/u. This is the inverse origin
ideal convention required by the desired Ta−O construction. -/
def infinityInverseRestriction (n : K) :
    infinityInversePushed n ⟶ overlapFunctionsPushed n :=
  ClutchedModule318.twistedRestriction (affineChart n) (infinityChart n)
    (intoAffine n) (intoInfinity n) (actual_original_overlap_square n) (inverseUSection n)

/-- ACTUAL global O-module sheaf of pairs: original affine root-ideal
sections and infinity coefficients, agreeing as functions with b/u on
the common chart. Local freeness and divisor identification are separate
obligations, not fields supplied in a purported line-bundle structure. -/
def originalRootIdealSheaf (n : K) (i : Fin 3) : (originalCubicScheme n).Modules :=
  pullback (affineIdealRestriction n i) (infinityInverseRestriction n)
def affineProjection (n : K) (i : Fin 3) :
    originalRootIdealSheaf n i ⟶ affineIdealPushed n i := pullback.fst _ _
def infinityProjection (n : K) (i : Fin 3) :
    originalRootIdealSheaf n i ⟶ infinityInversePushed n := pullback.snd _ _
lemma actual_ideal_sheaf_compatibility (n : K) (i : Fin 3) :
    affineProjection n i ≫ affineIdealRestriction n i=
      infinityProjection n i ≫ infinityInverseRestriction n := pullback.condition
end ActualTwoDescentOriginalDegreeZeroIdealSheaf318
