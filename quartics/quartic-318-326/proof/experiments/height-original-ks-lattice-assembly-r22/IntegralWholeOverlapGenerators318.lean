module
public import IntegralOriginalCommonRestriction318
public section
noncomputable section
namespace IntegralWholeOverlapGenerators318
open ThreeRootCoordinates318
open IntegralWholeReciprocalOrders318 IntegralWholeReciprocalOverlap318 IntegralWholeOrderOpenMaps318
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Type*} [CommRing S]

/-- Signed generator scaling on the full order, with no radicand-unit
hypothesis and hence without deleting the branch points. -/
theorem full_scale (a b : Fin 3 → S) (y : Sˣ) (h : ∀ j,b j=a j*(y:S)^2) (j : Fin 3) :
    UnitScaledQuadraticOrder318.three a b y h (generator b j)=(y:S) • generator a j := by
  fin_cases j <;>
    simp [UnitScaledQuadraticOrder318.three,generator,
      Algebra.TensorProduct.congr_apply,Algebra.TensorProduct.map_tmul,
      UnitScaledQuadraticOrder318.equiv_root,←AdjoinRoot.algebraMap_eq,←Algebra.smul_def,
      ←TensorProduct.smul_tmul',TensorProduct.tmul_smul]

universe u
/-- Evaluate the existing bundled base-change map on abstract carriers,
before a concrete Laurent carrier has two polynomial scalar actions. -/
private theorem baseChangedOrderMapAlong_generator {A T : Type u}
    [CommRing A] [CommRing T] (f : A →+* T) (a : Fin 3 → A) (j : Fin 3) :
    baseChangedOrderMapAlong f a (generator a j) =
      generator (fun i => f (a i)) j := by
  letI : Algebra A T := f.toAlgebra
  change coefficientMap a T (generator a j) = _
  exact coefficientMap_generator a T j

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)

theorem finite_generator (j : Fin 3) :
    finiteMap R c (generator (finiteCoefficient R c) j)=generator (finiteParameter R c) j :=
  coefficientMap_generator _ (Laurent R) j

/-- The full reciprocal inclusion sends each labeled ratio root to the
inverse pivot times the corresponding full finite root. -/
theorem infinity_generator (j : Fin 3) :
    infinityMap R c (generator (IntegralInfinityChart318.coefficient R c) j)=
      (↑(y R)⁻¹:Laurent R) • generator (finiteParameter R c) j := by
  change (fullOverlap R c).symm
    (baseChangedOrderMapAlong (reciprocalMap R c).toRingHom
      (IntegralInfinityChart318.coefficient R c)
      (generator (IntegralInfinityChart318.coefficient R c) j)) = _
  have hg : baseChangedOrderMapAlong (reciprocalMap R c).toRingHom
      (IntegralInfinityChart318.coefficient R c)
      (generator (IntegralInfinityChart318.coefficient R c) j) =
      generator (infinityParameter R c) j := by
    simpa only [infinityParameter,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using
      (baseChangedOrderMapAlong_generator (reciprocalMap R c).toRingHom
        (IntegralInfinityChart318.coefficient R c) j)
  have hs : fullOverlap R c (generator (finiteParameter R c) j) =
      (y R : Laurent R) • generator (infinityParameter R c) j := by
    simpa only [fullOverlap] using
      (full_scale (infinityParameter R c) (finiteParameter R c) (y R)
        (parameter_identity R c) j)
  rw [hg]
  apply (fullOverlap R c).injective
  rw [AlgEquiv.apply_symm_apply,map_smul,hs,smul_smul,Units.inv_mul,one_smul]

end IntegralWholeOverlapGenerators318
