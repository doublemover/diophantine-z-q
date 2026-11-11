module
public import FourSimpleQuadraticUniversal318
public import UnitQuadraticRootCoordinates318
public import IntegralRootPointMaps318
public import IntegralQuadraticPointZoom318
public section
noncomputable section
namespace QuadraticZoomRootOpen318
open scoped TensorProduct
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (q : Fin 4 → R) (p : Fin 4 → Rˣ)
  (two : Rˣ) (htwo : (two : R)=2)
@[expose] def coefficient (i : Fin 4) : R := (p i : R)^2*(1+4*q i)
abbrev Old := FourRootOrder318.Order (coefficient q p)
@[expose] def denominator : Old q p := ∏ i : Fin 4,FourRootOrderSigns318.generator (coefficient q p) i
abbrev OldOpen := Localization.Away (denominator q p)
abbrev New := FourSimpleQuadraticEtale318.Ring q
@[expose] def oldRoot (i : Fin 4) : OldOpen q p :=
  algebraMap (Old q p) (OldOpen q p) (FourRootOrderSigns318.generator (coefficient q p) i)
@[expose] def newRoot (i : Fin 4) : New q := FourSimpleQuadraticEtale318.generator q i
@[expose] def mappedUnit {S : Type*} [CommRing S] [Algebra R S] (u : Rˣ) : Sˣ :=
  Units.map (algebraMap R S).toMonoidHom u

theorem oldRoot_square (i : Fin 4) : (oldRoot q p i)^2=
    algebraMap R (OldOpen q p) (coefficient q p i) := by
  rw [oldRoot,←map_pow,FourRootOrderSigns318.generator_square,
    ←IsScalarTower.algebraMap_apply]

theorem oldRoot_unit (i : Fin 4) : IsUnit (oldRoot q p i) := by
  have hd := IsLocalization.Away.algebraMap_isUnit
    (S := OldOpen q p) (denominator q p)
  apply isUnit_of_dvd_unit _ hd
  obtain ⟨b,hb⟩ := Finset.dvd_prod_of_mem
    (fun j => FourRootOrderSigns318.generator (coefficient q p) j) (Finset.mem_univ i)
  exact ⟨algebraMap (Old q p) (OldOpen q p) b,by
    change algebraMap (Old q p) (OldOpen q p) (denominator q p)=_
    rw [hb,map_mul]
    rfl⟩

@[expose] def inverseRoot (i : Fin 4) : OldOpen q p :=
  UnitQuadraticRootCoordinates318.inverseCoordinate
    (mappedUnit (S := OldOpen q p) two) (mappedUnit (S := OldOpen q p) (p i)) (oldRoot q p i)

theorem inverseRoot_relation (i : Fin 4) : (inverseRoot q p two i)^2+inverseRoot q p two i=
    algebraMap R (OldOpen q p) (q i) := by
  apply UnitQuadraticRootCoordinates318.quadratic_relation
    (mappedUnit (S := OldOpen q p) two) (mappedUnit (S := OldOpen q p) (p i))
    (by change algebraMap R _ (two : R)=2; rw [htwo,map_ofNat])
  simpa only [coefficient,map_mul,map_add,map_pow,map_one,map_ofNat] using oldRoot_square q p i

theorem inverseRoot_derivative_unit (i : Fin 4) : IsUnit (2*inverseRoot q p two i+1) :=
  UnitQuadraticRootCoordinates318.derivative_unit
    (mappedUnit (S := OldOpen q p) two) (mappedUnit (S := OldOpen q p) (p i))
    (by change algebraMap R _ (two : R)=2; rw [htwo,map_ofNat]) _ (oldRoot_unit q p i)

@[expose] def backward : New q →ₐ[R] OldOpen q p :=
  FourSimpleQuadraticUniversal318.lift q (inverseRoot q p two)
    (inverseRoot_relation q p two htwo) (inverseRoot_derivative_unit q p two htwo)
@[expose] def forwardRoot (i : Fin 4) : New q :=
  algebraMap R (New q) (p i : R)*(1+2*newRoot q i)

theorem forwardRoot_square (i : Fin 4) : (forwardRoot q p i)^2=
    algebraMap R (New q) (coefficient q p i) := by
  rw [forwardRoot,IntegralQuadraticPointZoom318.root_identity _ _ _
    (FourSimpleQuadraticEtale318.generator_relation q i)]
  simp only [coefficient,map_mul,map_add,map_pow,map_one,map_ofNat]

theorem forwardRoot_unit (i : Fin 4) : IsUnit (forwardRoot q p i) := by
  exact ((p i).isUnit.map (algebraMap R (New q))).mul (by
    simpa only [add_comm] using FourSimpleQuadraticUniversal318.derivative_unit q i)

@[expose] def rawForward : Old q p →ₐ[R] New q :=
  IntegralRootPointMaps318.fourMap (coefficient q p) (forwardRoot q p) (forwardRoot_square q p)

theorem rawForward_denominator_unit : IsUnit (rawForward q p (denominator q p)) := by
  simp only [denominator,map_prod,rawForward,IntegralRootPointMaps318.fourMap_generator]
  classical
  induction (Finset.univ : Finset (Fin 4)) using Finset.induction_on with
  | empty => simpa using (isUnit_one : IsUnit (1 : New q))
  | @insert i s hi hs => rw [Finset.prod_insert hi]; exact (forwardRoot_unit q p i).mul hs

@[expose] def forward : OldOpen q p →ₐ[R] New q :=
  IsLocalization.Away.liftAlgHom (f := rawForward q p) (denominator q p)
    (rawForward_denominator_unit q p)

theorem forward_oldRoot (i : Fin 4) : forward q p (oldRoot q p i)=forwardRoot q p i := by
  simp only [forward,oldRoot,IsLocalization.Away.liftAlgHom_apply,
    IsLocalization.Away.lift_eq,rawForward,IntegralRootPointMaps318.fourMap_generator]

theorem backward_newRoot (i : Fin 4) : backward q p two htwo (newRoot q i)=inverseRoot q p two i :=
  FourSimpleQuadraticUniversal318.lift_generator _ _ _ _ i

theorem backward_forward_root (i : Fin 4) :
    backward q p two htwo (forward q p (oldRoot q p i))=oldRoot q p i := by
  rw [forward_oldRoot,forwardRoot,map_mul,map_add,map_one,map_mul,map_ofNat,
    AlgHom.commutes,backward_newRoot]
  exact UnitQuadraticRootCoordinates318.recover_original
    (mappedUnit (S := OldOpen q p) two) (mappedUnit (S := OldOpen q p) (p i))
    (by change algebraMap R _ (two : R)=2; rw [htwo,map_ofNat]) _

theorem forward_backward_root (i : Fin 4) :
    forward q p (backward q p two htwo (newRoot q i))=newRoot q i := by
  rw [backward_newRoot]
  change forward q p ((algebraMap R _ (↑two⁻¹ : R))*
    ((algebraMap R _ (↑(p i)⁻¹ : R))*oldRoot q p i-1))=_
  rw [map_mul,map_sub,map_mul,map_one,AlgHom.commutes,AlgHom.commutes,forward_oldRoot]
  exact UnitQuadraticRootCoordinates318.recover_new
    (mappedUnit (S := New q) two) (mappedUnit (S := New q) (p i))
    (by change algebraMap R _ (two : R)=2; rw [htwo,map_ofNat]) _

theorem backward_forward : (backward q p two htwo).comp (forward q p)=AlgHom.id R (OldOpen q p) := by
  apply AlgHom.toRingHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (denominator q p))
  apply IntegralRootPointMaps318.four_ringHom_ext
  · ext r
    simp only [RingHom.comp_apply,AlgHom.toRingHom_eq_coe,AlgHom.comp_apply,
      ←IsScalarTower.algebraMap_apply,AlgHom.commutes,AlgHom.id_apply]
  · intro i
    exact backward_forward_root q p two htwo i

theorem forward_backward : (forward q p).comp (backward q p two htwo)=AlgHom.id R (New q) := by
  apply FourSimpleQuadraticUniversal318.hom_ext
  exact forward_backward_root q p two htwo

/-- Actual algebra equivalence, proved on the complete coefficient ring
and every original marked root, not merely on field-valued points. -/
@[expose] def equivalence : OldOpen q p ≃ₐ[R] New q :=
  AlgEquiv.ofAlgHom (forward q p) (backward q p two htwo)
    (forward_backward q p two htwo) (backward_forward q p two htwo)
end QuadraticZoomRootOpen318
