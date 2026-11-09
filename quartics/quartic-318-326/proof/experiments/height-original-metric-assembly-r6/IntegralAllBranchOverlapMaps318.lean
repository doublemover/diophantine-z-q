module
public import IntegralGluedDifferentialFrames318
public section
noncomputable section
namespace IntegralAllBranchOverlapMaps318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralSourceBranches318 IntegralBranchDenominatorCover318
open IntegralOverlapChartMaps318 IntegralOverlapCoefficientRestrictions318
open IntegralOverlapOpenImmersions318 IntegralGluedModel318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
@[expose] def polynomialMap : R[X] →ₐ[R] Overlap R c :=
  (sourceMap R c).comp (IsScalarTower.toAlgHom R R[X] (SourceOrder R c))
@[expose] def P : Overlap R c := polynomialMap R c (IntegralBranchBicanonical318.quartic R)
@[expose] def t : Overlap R c := polynomialMap R c X

theorem polynomialMap_C (r : R) : polynomialMap R c (C r)=algebraMap R (Overlap R c) r :=
  (polynomialMap R c).commutes r

theorem t_original : t R c=commonMap R c (IntegralOverlapCoefficients318.originalT R c) :=
  finite_originalT R c

theorem t_unit : IsUnit (t R c) := by
  rw [t_original]
  apply IsUnit.map
  rw [IntegralOverlapCoefficients318.originalT,IntegralInfinityCommonBase318.polynomial_X]
  exact (((c 0)⁻¹).isUnit.map _).mul ((IntegralInfinityCommonBase318.rootUnit R c).isUnit.pow 2)

theorem denominator_zero_unit : IsUnit (polynomialMap R c (twisted R c 0)) := by
  have he : polynomialMap R c (twisted R c 0) =
      commonMap R c (IntegralOverlapCoefficients318.finiteDenominator R c) :=
    finite_denominator R c
  rw [he]
  exact (isUnit_iff_exists_inv.mpr
    ⟨IntegralOverlapCoefficients318.finiteInverse R c,IntegralOverlapCoefficients318.finite_inverse R c⟩).map _

/-- The same actual finite–infinity overlap inverts the original full quartic.
This uses the invertible root y0 and exact denominator, not a generic nonzero claim. -/
theorem P_unit : IsUnit (P R c) := by
  have h := congrArg (polynomialMap R c)
    (IntegralBranchBicanonical318.factor_product_polynomial R c 0)
  have h0 : contacts R 0=0 := rfl
  rw [h0,map_zero,sub_zero,map_mul,map_mul] at h
  have hu : IsUnit (polynomialMap R c X*polynomialMap R c (twisted R c 0)) :=
    (t_unit R c).mul (denominator_zero_unit R c)
  rw [h] at hu
  exact (isUnit_mul_iff.mp hu).2

/-- Every original branch denominator is a unit in this SAME integral overlap. -/
theorem denominator_unit (i : Fin 4) :
    IsUnit (sourceMap R c (denominator R c i)) := by
  have h := congrArg (polynomialMap R c)
    (IntegralBranchBicanonical318.factor_product_polynomial R c i)
  rw [map_mul,map_mul,polynomialMap_C] at h
  have hu : IsUnit (algebraMap R (Overlap R c) (twistUnit R c i : R)*P R c) :=
    ((twistUnit R c i).isUnit.map _).mul (P_unit R c)
  rw [←h] at hu
  exact (isUnit_mul_iff.mp hu).2

@[expose] def branchMap (i : Fin 4) : IntegralBranchCoordinates318.B R c i →ₐ[R] Overlap R c where
  __ := IsLocalization.Away.lift (g := (sourceMap R c).toRingHom)
    (denominator R c i) (denominator_unit R c i)
  commutes' r := by
    change IsLocalization.Away.lift (g := (sourceMap R c).toRingHom)
      (denominator R c i) (denominator_unit R c i)
      (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c i)
        (algebraMap R (SourceOrder R c) r)) = _
    rw [IsLocalization.Away.lift_eq]
    exact (sourceMap R c).commutes r

@[simp] theorem branchMap_source (i : Fin 4) (a : SourceOrder R c) :
    branchMap R c i (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c i) a) =
      sourceMap R c a := IsLocalization.Away.lift_eq _ _ _

theorem branchMap_polynomial (i : Fin 4) (q : R[X]) :
    branchMap R c i (algebraMap R[X] (IntegralBranchCoordinates318.B R c i) q) =
      polynomialMap R c q := by
  rw [IsScalarTower.algebraMap_apply R[X] (SourceOrder R c)
    (IntegralBranchCoordinates318.B R c i),branchMap_source]
  rfl

theorem branchMap_zero : branchMap R c 0=finiteMap R c := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator R c 0))
  apply RingHom.ext
  intro a
  exact branchMap_source R c 0 a

instance branchMap_open (i : Fin 4) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (branchMap R c i).toRingHom)) := by
  let f := Spec.map (CommRingCat.ofHom (branchMap R c i).toRingHom)
  let g := Spec.map (CommRingCat.ofHom
    (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c i)))
  have he : f ≫ g=intoFinite R c := by
    dsimp [f,g,intoFinite]
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact branchMap_source R c i
  letI : IsOpenImmersion g := IsOpenImmersion.of_isLocalization (denominator R c i)
  letI : IsOpenImmersion (f ≫ g) := by rw [he];infer_instance
  exact IsOpenImmersion.of_comp f g
end IntegralAllBranchOverlapMaps318
