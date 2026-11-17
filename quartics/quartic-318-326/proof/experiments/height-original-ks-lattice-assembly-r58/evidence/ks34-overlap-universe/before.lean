module
public import FourRootOrderOpenMaps318
public import IntegralFourRootReciprocalCharts318
public section
noncomputable section
namespace IntegralFourRootOverlap318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOverlap318
open IntegralFourRootReciprocalCharts318
variable (R : Type*) [CommRing R] (d a : Fin 4 → R)

/-- The previously proved Laurent inversion is used with auxiliary unit1;
these auxiliary units are not the twists d of the new integral model. -/
@[expose] def reciprocalMap : R[X] →ₐ[R] Laurent R :=
  IntegralWholeReciprocalOverlap318.reciprocalMap R (fun _ => 1)

theorem reciprocalMap_eval (p : R[X]) :
    reciprocalMap R p = Polynomial.aeval (((y R)⁻¹ : (Laurent R)ˣ) : Laurent R) p := by
  simp only [reciprocalMap, IntegralWholeReciprocalOverlap318.reciprocalMap,
    u, Units.val_one, map_one, one_mul]

theorem native_eval (p : R[X]) :
    Polynomial.aeval (y R : Laurent R) p = algebraMap R[X] (Laurent R) p := by
  have h : Polynomial.aeval (y R : Laurent R) =
      IsScalarTower.toAlgHom R R[X] (Laurent R) := by
    apply Polynomial.algHom_ext
    change Polynomial.aeval (y R : Laurent R) X = algebraMap R[X] (Laurent R) X
    rw [Polynomial.aeval_X, y_value]
  exact AlgHom.congr_fun h p

@[expose] def finiteParameter (i : Fin 4) : Laurent R :=
  algebraMap R[X] (Laurent R) (finiteCoefficient d a i)
@[expose] def reciprocalParameter (i : Fin 4) : Laurent R :=
  reciprocalMap R (reciprocalCoefficient d a i)

theorem parameter_identity (i : Fin 4) :
    reciprocalParameter R d a i = finiteParameter R d a i *
      (((y R)⁻¹ : (Laurent R)ˣ) : Laurent R)^2 := by
  have h := overlap_coefficient d a ((y R)⁻¹) i
  simpa only [reciprocalParameter, reciprocalMap_eval, finiteParameter,
    inv_inv, native_eval] using h

@[expose] def fullOverlap :
    FourRootOrder318.Order (reciprocalParameter R d a) ≃ₐ[Laurent R]
      FourRootOrder318.Order (finiteParameter R d a) :=
  IntegralScaledFourRootModel318.fourScale _ _ (fun _ => (y R)⁻¹)
    (parameter_identity R d a)

abbrev CommonOrder := FourRootOrder318.Order (finiteParameter R d a)

@[expose] def finiteMap : FiniteOrder d a →+* CommonOrder R d a :=
  FourRootOrderOpenMaps318.baseChangedOrderMap (T:=Laurent R) (finiteCoefficient d a)

instance finiteMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (finiteMap R d a))) :=
  FourRootOrderOpenMaps318.baseChangedOrderMap_open (T:=Laurent R)
    (finiteCoefficient d a) (X:R[X])

@[expose] def infinityMap : ReciprocalOrder d a →+* CommonOrder R d a :=
  (fullOverlap R d a).toRingHom.comp
    (FourRootOrderOpenMaps318.baseChangedOrderMapAlong (reciprocalMap R).toRingHom
      (reciprocalCoefficient d a))

/-- Establish the composition on abstract ring carriers before specializing
large four-root tensor dictionaries. The supplied open map and equivalence
are retained exactly. -/
private lemma equiv_after_open {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (e : B ≃+* C)
    (hf : IsOpenImmersion (Spec.map (CommRingCat.ofHom f))) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (e.toRingHom.comp f))) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom f)) := hf
  letI : IsIso (Spec.map e.toCommRingCatIso.hom) := inferInstance
  have h : Spec.map (CommRingCat.ofHom (e.toRingHom.comp f)) =
      Spec.map e.toCommRingCatIso.hom ≫ Spec.map (CommRingCat.ofHom f) := by
    rw [← Spec.map_comp]
    rfl
  rw [h]
  exact IsOpenImmersion.comp _ _

instance infinityMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (infinityMap R d a))) := by
  exact equiv_after_open
    (FourRootOrderOpenMaps318.baseChangedOrderMapAlong (reciprocalMap R).toRingHom
      (reciprocalCoefficient d a))
    (fullOverlap R d a).toRingEquiv
    (FourRootOrderOpenMaps318.baseChangedOrderMapAlong_open (reciprocalMap R).toRingHom
      (reciprocalCoefficient d a) (X:R[X])
      (IntegralWholeReciprocalLocalization318.reciprocal_localization R (fun _ => 1)))

end IntegralFourRootOverlap318
