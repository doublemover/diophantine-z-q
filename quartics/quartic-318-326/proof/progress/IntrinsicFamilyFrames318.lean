module
public import FamilyOpenRestriction318
public import GlobalInvariantLine318
public section
noncomputable section
namespace IntrinsicFamilyFrames318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R] (A B : R)

theorem finite_structure (i : Fin 2) :
    InvariantChartCover318.finiteInto A B i ≫ WeierstrassGluing318.structureMap A B =
      Spec.map (CommRingCat.ofHom (algebraMap R (WeierstrassKaehler318.AffineChart A B i))) := by
  unfold InvariantChartCover318.finiteInto
  rw [Category.assoc,WeierstrassGluing318.finiteChart_structure]
  unfold ShortAffineScheme318.structureMap
  rw [←Spec.map_comp]
  congr 1

theorem infinity_structure :
    InvariantChartCover318.infinityInto A B ≫ WeierstrassGluing318.structureMap A B =
      Spec.map (CommRingCat.ofHom (algebraMap R (DifferentialChartMaps318.InfinityChart A B))) := by
  unfold InvariantChartCover318.infinityInto
  rw [Category.assoc,WeierstrassGluing318.infinityChart_structure]
  unfold InfinitySmooth318.structureMap
  rw [←Spec.map_comp]
  congr 1

/-- Actual restriction of intrinsic global Omega to the x chart, identified with
its ordinary algebraic differential sheaf. -/
@[expose] def xIdentification :
    (FamilyIntrinsicDifferentials318.familyOmega A B).restrict
      (InvariantChartCover318.finiteInto A B 0) ≅
        AffineDifferentialSheaf318.differentialSheaf
          (R:=R) (S:=FiniteInvariantDifferential318.XChart A B) :=
  FamilyOpenRestriction318.restrictIso _ _ ≪≫
    eqToIso (congrArg FamilyIntrinsicDifferentials318.omega (finite_structure A B 0)) ≪≫
      AffineIntrinsicFrames318.algebraIso.symm

@[expose] def finiteIdentification :
    (FamilyIntrinsicDifferentials318.familyOmega A B).restrict
      (InvariantChartCover318.finiteInto A B 1) ≅
        AffineDifferentialSheaf318.differentialSheaf
          (R:=R) (S:=DifferentialChartMaps318.FiniteChart A B) :=
  FamilyOpenRestriction318.restrictIso _ _ ≪≫
    eqToIso (congrArg FamilyIntrinsicDifferentials318.omega (finite_structure A B 1)) ≪≫
      AffineIntrinsicFrames318.algebraIso.symm

@[expose] def infinityIdentification :
    (FamilyIntrinsicDifferentials318.familyOmega A B).restrict
      (InvariantChartCover318.infinityInto A B) ≅
        AffineDifferentialSheaf318.differentialSheaf
          (R:=R) (S:=DifferentialChartMaps318.InfinityChart A B) :=
  FamilyOpenRestriction318.restrictIso _ _ ≪≫
    eqToIso (congrArg FamilyIntrinsicDifferentials318.omega (infinity_structure A B)) ≪≫
      AffineIntrinsicFrames318.algebraIso.symm

/-- Intrinsic global Omega and the invariant line agree on the actual x chart. -/
@[expose] def xLineIso := xIdentification A B ≪≫
  (GlobalInvariantLine318.xIdentification A B).symm
@[expose] def finiteLineIso := finiteIdentification A B ≪≫
  (GlobalInvariantLine318.finiteIdentification A B).symm
@[expose] def infinityLineIso := infinityIdentification A B ≪≫
  (GlobalInvariantLine318.infinityIdentification A B).symm

/-- These intrinsic rank-one identifications cover every point of the actual
smooth complete family. This is a proved local conclusion, not yet a global frame. -/
theorem identification_cover (hD : IsUnit (-16*(4*A^3+27*B^2)))
    (p : WeierstrassGluing318.scheme A B) :
    (∃ i, ∃ q, InvariantChartCover318.finiteInto A B i q=p) ∨
      (∃ q, InvariantChartCover318.infinityInto A B q=p) :=
  InvariantChartCover318.charts_cover A B hD p
end IntrinsicFamilyFrames318
