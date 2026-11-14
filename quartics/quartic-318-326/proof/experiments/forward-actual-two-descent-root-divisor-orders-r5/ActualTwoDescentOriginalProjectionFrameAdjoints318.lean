module
public import ActualTwoDescentOpenRestrictionAdjointComposition318
public section
noncomputable section
namespace ActualTwoDescentOriginalProjectionFrameAdjoints318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalDegreeZeroIdealSheaf318
open ActualTwoDescentOriginalRootAffineSheaf318 ActualTwoDescentOriginalIdealAffineRestriction318
open ActualTwoDescentOriginalIdealInfinityFrame318 ActualTwoDescentOpenRestrictionAdjointComposition318
universe u
variable {K : Type u} [Field K] [CharZero K]

lemma actual_affine_frame_adjoint (n : K) (i : Fin 3) :
    (Scheme.Modules.restrictAdjunction (affineChart n)).homEquiv _ _
      (originalAffineRestrictionIso n i).hom=affineProjection n i :=
  localMap_adjoint (affineChart n) (originalRootIdealSheaf n i) (rootAffineSheaf n i) (affineProjection n i)

lemma actual_infinity_frame_adjoint (n : K) (i : Fin 3) :
    (Scheme.Modules.restrictAdjunction (infinityChart n)).homEquiv _ _
      (originalInfinityFrame n i).hom=infinityProjection n i :=
  localMap_adjoint (infinityChart n) (originalRootIdealSheaf n i)
    (SheafOfModules.unit (infinityScheme n).ringCatSheaf) (infinityProjection n i)

/-- The actual old affine projection followed by the literal original
ideal inclusion,still on the whole original affine chart. -/
def affineInclusionFrame (n : K) (i : Fin 3) :
    (originalRootIdealSheaf n i).restrict (affineChart n) ⟶
      SheafOfModules.unit (affineScheme n).ringCatSheaf :=
  (originalAffineRestrictionIso n i).hom ≫ rootAffineInclusion n i

lemma actual_affine_inclusion_adjoint (n : K) (i : Fin 3) :
    (Scheme.Modules.restrictAdjunction (affineChart n)).homEquiv _ _
      (affineInclusionFrame n i)=affineProjection n i ≫
        (Scheme.Modules.pushforward (affineChart n)).map (rootAffineInclusion n i) := by
  rw [affineInclusionFrame,Adjunction.homEquiv_naturality_right,actual_affine_frame_adjoint]
end ActualTwoDescentOriginalProjectionFrameAdjoints318
