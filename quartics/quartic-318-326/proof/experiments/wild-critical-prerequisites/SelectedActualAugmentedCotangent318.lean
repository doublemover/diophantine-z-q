module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.RingTheory.Ideal.Cotangent
import all Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.Tactic.Ring
public section
noncomputable section

namespace SelectedActualAugmentedCotangent318

universe u
variable {R V : Type u} [CommRing R] [AddCommGroup V] [Module R V]

/-- The same R-module viewed with the canonical opposite scalar action,
scoped only to the actual split affine tests below. -/
scoped instance testOpposite : Module Rᵐᵒᵖ V :=
  Module.compHom V (RingEquiv.toOpposite R).symm.toRingHom

open scoped SelectedActualAugmentedCotangent318

scoped instance testCentral : IsCentralScalar R V where
  op_smul_eq_smul _ _ := rfl

variable {A : Type u} [CommRing A] [Algebra R A]
variable (aug : A →ₐ[R] R)

abbrev I := RingHom.ker aug.toRingHom
abbrev cotangent := (I aug).Cotangent

private def difference (a : A) : I aug :=
  ⟨a-algebraMap R A (aug a),by
    change aug (a-algebraMap R A (aug a)) = 0
    rw [map_sub,aug.commutes,sub_self]⟩

private def projection : A →ₗ[R] I aug :=
  (LinearMap.id - (Algebra.linearMap R A).comp aug.toLinearMap).codRestrict
    ((I aug).restrictScalars R) (fun a => (difference aug a).prop)

/-- Class of a minus its literal coefficient at the identity. -/
def dAug : A →ₗ[R] cotangent aug :=
  ((I aug).toCotangent.restrictScalars R).comp (projection aug)

private theorem d_on_ideal (x : I aug) : dAug aug (x:A) = (I aug).toCotangent x := by
  change (I aug).toCotangent (difference aug (x:A)) = _
  congr 1
  apply Subtype.ext
  change (x:A)-algebraMap R A (aug (x:A)) = (x:A)
  have h : aug (x:A)=0 := x.prop
  rw [h,map_zero,sub_zero]

private theorem d_on_scalar (r : R) : dAug aug (algebraMap R A r) = 0 := by
  change (I aug).toCotangent (difference aug (algebraMap R A r)) = 0
  have h : difference aug (algebraMap R A r) = 0 := by
    apply Subtype.ext
    change algebraMap R A r - algebraMap R A (aug (algebraMap R A r)) = 0
    rw [aug.commutes,sub_self]
  rw [h,map_zero]

theorem dAug_surjective : Function.Surjective (dAug aug) := by
  intro x
  obtain ⟨t,rfl⟩ := (I aug).toCotangent_surjective x
  exact ⟨t,d_on_ideal aug t⟩

private theorem d_mul (a b : A) :
    dAug aug (a*b) = aug a • dAug aug b + aug b • dAug aug a := by
  let v : I aug := aug a • difference aug b + aug b • difference aug a
  have h : (I aug).toCotangent (difference aug (a*b)) = (I aug).toCotangent v := by
    apply (Ideal.toCotangent_eq (I aug)).2
    change (a*b-algebraMap R A (aug (a*b))) -
      (aug a • (b-algebraMap R A (aug b))+
       aug b • (a-algebraMap R A (aug a))) ∈ (I aug)^2
    simp only [Algebra.smul_def,map_mul]
    have hpol : a*b-algebraMap R A (aug a)*algebraMap R A (aug b) -
      (algebraMap R A (aug a)*(b-algebraMap R A (aug b))+
       algebraMap R A (aug b)*(a-algebraMap R A (aug a))) =
        (a-algebraMap R A (aug a))*(b-algebraMap R A (aug b)) := by ring
    rw [hpol,pow_two]
    exact Ideal.mul_mem_mul (difference aug a).prop (difference aug b).prop
  change (I aug).toCotangent (difference aug (a*b)) =
    aug a • (I aug).toCotangent (difference aug b) +
      aug b • (I aug).toCotangent (difference aug a)
  rw [h]
  change ((I aug).toCotangent.restrictScalars R)
      (aug a • difference aug b+aug b • difference aug a) = _
  rw [map_add,map_smul,map_smul] <;> rfl

/-- Canonical map to the trivial first neighborhood of the same
augmentation. This records actual coordinates, not an abstract
identification of test-point cardinalities. -/
def universal : A →ₐ[R] TrivSqZeroExt R (cotangent aug) where
  toFun a := ⟨aug a,dAug aug a⟩
  map_zero' := TrivSqZeroExt.ext (map_zero aug) (map_zero (dAug aug))
  map_one' := TrivSqZeroExt.ext (map_one aug) (by
    change dAug aug (1:A) = 0
    rw [← map_one (algebraMap R A)]
    exact d_on_scalar aug 1)
  map_add' a b := TrivSqZeroExt.ext (map_add aug a b) (map_add (dAug aug) a b)
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul aug a b
    · exact d_mul aug a b
  commutes' r := by
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    exact TrivSqZeroExt.ext (aug.commutes r) (d_on_scalar aug r)

@[simp] theorem universal_fst (a : A) : (universal aug a).fst = aug a := rfl
@[simp] theorem universal_snd (a : A) : (universal aug a).snd = dAug aug a := rfl

abbrev quotientTest (v : cotangent aug) :=
  cotangent aug ⧸ Submodule.span R {v}

abbrev quotientMap (v : cotangent aug) : cotangent aug →ₗ[R] quotientTest aug v :=
  (Submodule.span R {v}).mkQ

/-- A single square-zero quotient test verifies that the chosen tangent
coordinate generates the global conormal. The actual projected zero
map is required, so no finite or geometric-field approximation can
supply this equality. -/
theorem global_generator_from_zero_test (v : cotangent aug) (M : ℕ) (hv : M • v=0)
    (hzero : (TrivSqZeroExt.map (quotientMap aug v)).comp (universal aug) =
      (Algebra.ofId R (TrivSqZeroExt R (quotientTest aug v))).comp aug) :
    ∃ t : A, t ∈ I aug ∧ I aug = Ideal.span {t} ⊔ (I aug)^2 ∧
      (algebraMap R A (M:R))*t ∈ (I aug)^2 := by
  obtain ⟨t,ht⟩ := (I aug).toCotangent_surjective v
  have span_all (x : I aug) : (I aug).toCotangent x ∈ Submodule.span R {v} := by
    have h := congrArg (fun f : A →ₐ[R] TrivSqZeroExt R (quotientTest aug v) => (f (x:A)).snd) hzero
    simp only [AlgHom.comp_apply,TrivSqZeroExt.snd_map,universal_snd,Algebra.ofId_apply,
      TrivSqZeroExt.algebraMap_eq_inl,TrivSqZeroExt.snd_inl,d_on_ideal] at h
    exact (Submodule.Quotient.mk_eq_zero _).1 h
  refine ⟨t,t.prop,?_,?_⟩
  · apply le_antisymm _ (sup_le (Ideal.span_singleton_le_iff_mem.2 t.prop)
      (Ideal.pow_le_self (by decide : (2:ℕ)≠0)))
    intro x hx
    let xI : I aug := ⟨x,hx⟩
    obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp (span_all xI)
    have he : (I aug).toCotangent xI = (I aug).toCotangent (r • t) := by
      have h : (I aug).toCotangent (r • t) = r • (I aug).toCotangent t :=
        map_smul ((I aug).toCotangent.restrictScalars R) r t
      rw [h,ht,hr]
    have hp : x - (algebraMap R A r)*(t:A) ∈ (I aug)^2 := by
      have hraw := (Ideal.toCotangent_eq (I aug)).1 he
      change x - r • (t:A) ∈ (I aug)^2 at hraw
      rwa [Algebra.smul_def] at hraw
    exact Submodule.mem_sup.2 ⟨_,Ideal.mem_span_singleton'.2 ⟨algebraMap R A r,rfl⟩,
      _,hp,by ring⟩
  · have hzero' : (I aug).toCotangent ((M:R) • t) = 0 := by
      have h : (I aug).toCotangent ((M:R) • t) = (M:R) • (I aug).toCotangent t :=
        map_smul ((I aug).toCotangent.restrictScalars R) (M:R) t
      rw [h,ht,Nat.cast_smul_eq_nsmul R]
      exact hv
    have hraw := (Ideal.toCotangent_eq_zero _ _).1 hzero'
    change (M:R) • (t:A) ∈ (I aug)^2 at hraw
    rwa [Algebra.smul_def] at hraw

end SelectedActualAugmentedCotangent318

#print axioms SelectedActualAugmentedCotangent318.dAug_surjective
#print axioms SelectedActualAugmentedCotangent318.global_generator_from_zero_test
