module
public import IntegralInfinityReverseBase318
public section
noncomputable section
namespace IntegralInfinityBaseEquiv318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318
open IntegralInfinityCommonOrder318 IntegralInfinityReverseBase318
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ring maps preserve the inverse of an explicitly specified unit. -/
theorem map_unit_inverse {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (a : Aˣ) (b : Bˣ) (h : f (a:A) = (b:B)) :
    f (↑a⁻¹ : A) = (↑b⁻¹ : B) := by
  have he : Units.map f.toMonoidHom a = b := Units.ext h
  exact congrArg (fun v : Bˣ => (↑v⁻¹ : B)) he

theorem map_reciprocal_unit {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (c : Rˣ) (a : Aˣ) (b : Bˣ)
    (h : f (a:A) = (b:B)) :
    f (↑(Units.map (algebraMap R A).toMonoidHom c * a⁻¹) : A) =
      (↑(Units.map (algebraMap R B).toMonoidHom c * b⁻¹) : B) := by
  simp only [Units.val_mul,Units.coe_map,map_mul,AlgHom.commutes]
  rw [map_unit_inverse f.toRingHom a b h]

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem finite_reciprocal :
    finiteOverlapMap R c (reciprocalUnit R c : CommonBase R c) =
      (infinityUnit R c : InfinityOverlap R c) := by
  have h := map_reciprocal_unit (finiteOverlapMap R c) (c 0)
    (rootUnit R c) (finiteUnit R c) (finiteOverlapMap_root R c)
  have he : Units.map (algebraMap R (InfinityOverlap R c)).toMonoidHom (c 0) *
      (finiteUnit R c)⁻¹ = infinityUnit R c := by
    unfold finiteUnit
    group
  exact h.trans (congrArg (fun v : (InfinityOverlap R c)ˣ => (v:InfinityOverlap R c)) he)

theorem infinity_finite :
    infinityOverlapMap R c (finiteUnit R c : InfinityOverlap R c) =
      (rootUnit R c : CommonBase R c) := by
  have h := map_reciprocal_unit (infinityOverlapMap R c) (c 0)
    (infinityUnit R c) (reciprocalUnit R c) (infinityOverlapMap_root R c)
  have he : Units.map (algebraMap R (CommonBase R c)).toMonoidHom (c 0) *
      (reciprocalUnit R c)⁻¹ = rootUnit R c := by
    unfold reciprocalUnit
    group
  exact h.trans (congrArg (fun v : (CommonBase R c)ˣ => (v:CommonBase R c)) he)

theorem finite_polynomial :
    (finiteOverlapMap R c).comp (reciprocalPolynomial R c) =
      IsScalarTower.toAlgHom R R[X] (InfinityOverlap R c) := by
  apply Polynomial.algHom_ext
  simp only [AlgHom.comp_apply,reciprocalPolynomial,Polynomial.aeval_X,
    IsScalarTower.toAlgHom_apply]
  rw [finite_reciprocal,infinityUnit_value,←IsScalarTower.algebraMap_apply]

theorem infinity_rootBase (a : BranchBase R c 0) :
    infinityOverlapMap R c (rootBaseMap R c a) = algebraMap (BranchBase R c 0) (CommonBase R c) a := by
  let e := LinearRootCoordinate318.coordinateEquiv (c 0) (contacts R 0)
  have hp : ((infinityOverlapMap R c).comp (rootBaseMap R c)).comp e.symm.toAlgHom =
      (IsScalarTower.toAlgHom R (BranchBase R c 0) (CommonBase R c)).comp e.symm.toAlgHom := by
    apply Polynomial.algHom_ext
    change infinityOverlapMap R c
      (Polynomial.aeval (finiteUnit R c : InfinityOverlap R c) (e (e.symm X))) =
        algebraMap (BranchBase R c 0) (CommonBase R c) (e.symm X)
    rw [e.apply_symm_apply,Polynomial.aeval_X,infinity_finite,rootUnit_value,rootOpen,
      ←IsScalarTower.algebraMap_apply]
    change algebraMap (BranchBase R c 0) (CommonBase R c) _ =
      algebraMap (BranchBase R c 0) (CommonBase R c) (e.symm X)
    congr 1
    exact (LinearRootCoordinate318.inverse_X (c 0) (contacts R 0)).symm
  simpa only [AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.symm_apply_apply,
    IsScalarTower.toAlgHom_apply] using AlgHom.congr_fun hp (e a)

theorem finite_infinity_inverse :
    (finiteOverlapMap R c).toRingHom.comp (infinityOverlapMap R c).toRingHom =
      RingHom.id (InfinityOverlap R c) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (algebraMap R[X] (IntegralInfinityChart318.Base R c) X))
  apply IsLocalization.ringHom_ext (Submonoid.powers (IntegralInfinityChart318.denominator R c))
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply,RingHom.id_apply,infinityOverlapMap_on_base,
    infinityBaseMap_polynomial,←IsScalarTower.algebraMap_apply]
  exact AlgHom.congr_fun (finite_polynomial R c) p

theorem infinity_finite_inverse :
    (infinityOverlapMap R c).toRingHom.comp (finiteOverlapMap R c).toRingHom =
      RingHom.id (CommonBase R c) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (rootOpen R c))
  apply IsLocalization.ringHom_ext (Submonoid.powers
    (IntegralBranchChart318.denominator (c 0) (contacts R 0)
      (otherTwist R c 0) (otherContact R 0)))
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply,RingHom.id_apply,finiteOverlapMap_on_base,
    finiteBaseMap_on_rootBase,←IsScalarTower.algebraMap_apply]
  exact infinity_rootBase R c a

/-- The actual finite y0≠0 coefficient base and actual infinity u≠0 base
are inverse algebraic localizations, with y0*u=c0 and original scalar maps. -/
@[expose] def baseEquiv : CommonBase R c ≃ₐ[R] InfinityOverlap R c :=
  AlgEquiv.ofAlgHom (finiteOverlapMap R c) (infinityOverlapMap R c)
    (by ext x;exact RingHom.congr_fun (finite_infinity_inverse R c) x)
    (by ext x;exact RingHom.congr_fun (infinity_finite_inverse R c) x)

local instance infinityAlgebra :
    Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra

@[expose] def baseEquivOverInfinity :
    CommonBase R c ≃ₐ[IntegralInfinityChart318.Base R c] InfinityOverlap R c where
  __ := (baseEquiv R c).toRingEquiv
  commutes' a := by
    have h := RingHom.congr_fun (finite_infinity_inverse R c)
      (algebraMap (IntegralInfinityChart318.Base R c) (InfinityOverlap R c) a)
    simpa only [RingHom.comp_apply,RingHom.id_apply,infinityOverlapMap_on_base] using h

/-- The original common base is exactly the infinity principal localization,
not merely an algebra receiving a map from that principal open. -/
theorem common_isInfinityLocalization :
    IsLocalization.Away (algebraMap R[X] (IntegralInfinityChart318.Base R c) X) (CommonBase R c) :=
  IsLocalization.isLocalization_of_algEquiv
    (S := InfinityOverlap R c)
    (Submonoid.powers (algebraMap R[X] (IntegralInfinityChart318.Base R c) X))
    (baseEquivOverInfinity R c).symm

end IntegralInfinityBaseEquiv318
