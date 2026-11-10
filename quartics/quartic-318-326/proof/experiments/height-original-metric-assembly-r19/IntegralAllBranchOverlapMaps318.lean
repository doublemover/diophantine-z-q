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
/-- The ordinary localization lift, with its native scalar square proved before
specializing to the original tensor-product overlap. -/
@[expose] def nativeAwayMap {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
    [Algebra A S] [Algebra A T] (f : S →ₐ[A] T) (d : S) (hd : IsUnit (f d)) :
    Localization.Away d →ₐ[A] T where
  __ := IsLocalization.Away.lift (g := f.toRingHom) d hd
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply A S (Localization.Away d)]
    exact (IsLocalization.Away.lift_eq d hd (algebraMap A S a)).trans (f.commutes a)

@[simp] theorem nativeAwayMap_source {A S T : Type*} [CommRing A] [CommRing S]
    [CommRing T] [Algebra A S] [Algebra A T] (f : S →ₐ[A] T) (d : S)
    (hd : IsUnit (f d)) (s : S) :
    nativeAwayMap f d hd (algebraMap S (Localization.Away d) s) = f s :=
  IsLocalization.Away.lift_eq d hd s

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance overlapCommRing : CommRing (Overlap R c) := inferInstance
local instance overlapAlgebra : Algebra R (Overlap R c) := inferInstance
local instance sourceCommRing : CommRing (SourceOrder R c) := inferInstance
local instance branchCommRing (i : Fin 4) :
    CommRing (IntegralBranchCoordinates318.B R c i) := inferInstance
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
  have hu : IsUnit (IntegralOverlapCoefficients318.originalT R c) := by
    rw [IntegralOverlapCoefficients318.originalT,IntegralInfinityCommonBase318.polynomial_X]
    exact (((c 0)⁻¹).isUnit.map _).mul ((IntegralInfinityCommonBase318.rootUnit R c).isUnit.pow 2)
  exact hu.map (commonMap R c).toRingHom

theorem denominator_zero_unit : IsUnit (polynomialMap R c (twisted R c 0)) := by
  have he : polynomialMap R c (twisted R c 0) =
      commonMap R c (IntegralOverlapCoefficients318.finiteDenominator R c) :=
    finite_denominator R c
  rw [he]
  exact (isUnit_iff_exists_inv.mpr
    ⟨IntegralOverlapCoefficients318.finiteInverse R c,IntegralOverlapCoefficients318.finite_inverse R c⟩).map (commonMap R c).toRingHom

/-- The same actual finite–infinity overlap inverts the original full quartic.
This uses the invertible root y0 and exact denominator, not a generic nonzero claim. -/
theorem P_unit : IsUnit (P R c) := by
  have hp : X * twisted R c 0 =
      C (twistUnit R c 0 : R) * IntegralBranchBicanonical318.quartic R := by
    simpa only [show contacts R 0 = 0 from rfl, map_zero, sub_zero] using
      IntegralBranchBicanonical318.factor_product_polynomial R c 0
  have h := congrArg (polynomialMap R c) hp
  rw [map_mul,map_mul] at h
  have hu : IsUnit (polynomialMap R c X*polynomialMap R c (twisted R c 0)) :=
    (t_unit R c).mul (denominator_zero_unit R c)
  rw [h] at hu
  change IsUnit (polynomialMap R c (IntegralBranchBicanonical318.quartic R))
  exact isUnit_of_mul_isUnit_right hu

/-- Every original branch denominator is a unit in this SAME integral overlap. -/
theorem denominator_unit (i : Fin 4) :
    IsUnit (sourceMap R c (denominator R c i)) := by
  have h := congrArg (polynomialMap R c)
    (IntegralBranchBicanonical318.factor_product_polynomial R c i)
  rw [map_mul,map_mul,polynomialMap_C] at h
  have hu : IsUnit (algebraMap R (Overlap R c) (twistUnit R c i : R)*P R c) :=
    ((twistUnit R c i).isUnit.map _).mul (P_unit R c)
  change IsUnit (algebraMap R (Overlap R c) (twistUnit R c i : R)*
    polynomialMap R c (IntegralBranchBicanonical318.quartic R)) at hu
  rw [←h] at hu
  change IsUnit (polynomialMap R c (twisted R c i))
  exact isUnit_of_mul_isUnit_right hu

@[expose] def branchMap (i : Fin 4) : IntegralBranchCoordinates318.B R c i →ₐ[R] Overlap R c :=
  nativeAwayMap (sourceMap R c) (denominator R c i) (denominator_unit R c i)

@[simp] theorem branchMap_source (i : Fin 4) (a : SourceOrder R c) :
    branchMap R c i (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c i) a) =
      sourceMap R c a := nativeAwayMap_source _ _ _ a

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
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (show IntegralBranchCoordinates318.B R c i →+* Overlap R c from (branchMap R c i).toRingHom))) := by
  let f := Spec.map (CommRingCat.ofHom (show IntegralBranchCoordinates318.B R c i →+* Overlap R c from (branchMap R c i).toRingHom))
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
