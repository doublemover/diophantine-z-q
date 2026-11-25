module
public import OriginalActualOriginAffineJet318
public import Mathlib.LinearAlgebra.Prod

@[expose] public section
noncomputable section

namespace OriginalActualOriginLieAddition318

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open OriginalAffineOriginCotangent318 OriginalAffineOriginFirstOrder318 OriginalActualOriginAffineJet318

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {A : Over (Spec (.of R))} [MonObj A] {e : B →ₐ[R] R}
variable (C : Chart R A e)

private def toThick {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (l : M →ₗ[R] N) :
    (Over.mk (testBase R N)) ⟶ (Over.mk (testBase R M)) :=
  Over.homMk (sp (TrivSqZeroExt.map l).toRingHom) (by
    rw [testBase, testBase, sp_comp]
    congr 1
    ext r
    exact (TrivSqZeroExt.map l).commutes r)

private theorem toThick_at_zero {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (l : M →ₗ[R] N) :
    zeroSection R N ≫ (toThick l).left = zeroSection R M := by
  change sp (TrivSqZeroExt.fstHom R R N).toRingHom ≫ sp (TrivSqZeroExt.map l).toRingHom =
    sp (TrivSqZeroExt.fstHom R R M).toRingHom
  rw [sp_comp]
  exact congrArg (fun f : Thick R M →ₐ[R] R => sp f.toRingHom)
    (TrivSqZeroExt.fstHom_comp_map l)

def push {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (l : M →ₗ[R] N) (x : ActualBased (A := A) M) : ActualBased (A := A) N :=
  ⟨toThick l ≫ x.1, by
    rw [Over.comp_left, ← Category.assoc, toThick_at_zero, x.2]⟩

/-- The chart's actual square-zero points depend naturally on the module.
The map on the underlying group is precomposition by the literal Spec
of the linear map of square-zero algebras. -/
theorem chart_natural {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (l : M →ₗ[R] N) (v : Cot e →ₗ[R] M) :
    push l (actual C v) = actual C (l.comp v) := by
  apply Subtype.ext
  apply Over.OverMorphism.ext
  change (toThick l).left ≫ (actual C v).1.left = (actual C (l.comp v)).1.left
  rw [actual_left, actual_left, ← Category.assoc]
  change (sp (TrivSqZeroExt.map l).toRingHom ≫
    sp ((points (S := R) e v).1).toRingHom) ≫ C.incl = _
  rw [sp_comp]
  have h : (TrivSqZeroExt.map l).comp (points (S := R) e v).1 =
      (points (S := R) e (l.comp v)).1 := by
    apply AlgHom.ext
    intro b
    apply TrivSqZeroExt.ext
    · simp only [AlgHom.comp_apply, TrivSqZeroExt.fst_map]
      exact (congrArg (fun f : B →ₐ[R] R => f b) ((points (S := R) e v).2)).trans
        (congrArg (fun f : B →ₐ[R] R => f b)
          ((points (S := R) e (l.comp v)).2)).symm
    · simp only [AlgHom.comp_apply, TrivSqZeroExt.snd_map, points_snd, LinearMap.comp_apply]
  exact congrArg (fun f : B →ₐ[R] Thick R N => sp f.toRingHom ≫ C.incl) h

private def zeroOver (M : Type u) [AddCommGroup M] [Module R M] :
    𝟙_ (Over (Spec (.of R))) ⟶ Over.mk (testBase R M) :=
  Over.homMk (zeroSection R M) (by
    rw [testBase, zeroSection, sp_comp]
    have h : (TrivSqZeroExt.fstHom R R M).toRingHom.comp (algebraMap R (Thick R M)) =
        RingHom.id R := by ext; rfl
    rw [h, sp, CommRingCat.ofHom_id, Spec.map_id])

private theorem is_based {M : Type u} [AddCommGroup M] [Module R M]
    (q : ActualBased (A := A) M) : zeroOver M ≫ q.1 = 1 := by
  rw [← MonObj.one_eq_one A]
  apply Over.OverMorphism.ext
  exact q.2

private def mul {M : Type u} [AddCommGroup M] [Module R M]
    (x y : ActualBased (A := A) M) : ActualBased (A := A) M :=
  ⟨x.1 * y.1, by
    have h : zeroOver M ≫ (x.1 * y.1) = η[A] := by
      rw [MonObj.comp_mul, is_based x, is_based y, mul_one, MonObj.one_eq_one A]
    exact congrArg Over.Hom.left h⟩

private theorem push_mul {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (l : M →ₗ[R] N) (x y : ActualBased (A := A) M) :
    push l (mul x y) = mul (push l x) (push l y) := by
  apply Subtype.ext
  exact MonObj.comp_mul (toThick l) x.1 y.1

private theorem chart_zero {M : Type u} [AddCommGroup M] [Module R M] :
    (actual C (0 : Cot e →ₗ[R] M)).1 = 1 := by
  apply Over.OverMorphism.ext
  rw [actual_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom]
  have h : (points (S := R) e (0 : Cot e →ₗ[R] M)).1 =
      (Algebra.ofId R (Thick R M)).comp e := by
    apply AlgHom.ext
    intro b
    apply TrivSqZeroExt.ext
    · exact congrArg (fun f : B →ₐ[R] R => f b) ((points (S := R) e (0 : Cot e →ₗ[R] M)).2)
    · rw [points_snd]; rfl
  rw [h]
  change sp ((algebraMap R (Thick R M)).comp e.toRingHom) ≫ C.incl =
    sp (algebraMap R (Thick R M)) ≫ (η[A]).left
  rw [← sp_comp, Category.assoc, C.origin]

/-- Coordinates of the actual represented group operation, with all terms
at the same actual unit. No assumption that the chosen affine chart is
a subgroup or that either endomorphism preserves that chart globally. -/
def operated {M : Type u} [AddCommGroup M] [Module R M] (v w : Cot e →ₗ[R] M) :
    Cot e →ₗ[R] M := (actual C).symm (mul (actual C v) (actual C w))

private theorem operated_natural {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (l : M →ₗ[R] N) (v w : Cot e →ₗ[R] M) :
    l.comp (operated C v w) = operated C (l.comp v) (l.comp w) := by
  apply (actual C).injective
  rw [← chart_natural]
  unfold operated
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, push_mul, chart_natural, chart_natural]

private theorem operated_left {M : Type u} [AddCommGroup M] [Module R M]
    (v : Cot e →ₗ[R] M) : operated C v 0 = v := by
  apply (actual C).injective
  apply Subtype.ext
  unfold operated
  rw [Equiv.apply_symm_apply]
  change (actual C v).1 * (actual C (0 : Cot e →ₗ[R] M)).1 = (actual C v).1
  rw [chart_zero, mul_one]

private theorem operated_right {M : Type u} [AddCommGroup M] [Module R M]
    (v : Cot e →ₗ[R] M) : operated C 0 v = v := by
  apply (actual C).injective
  apply Subtype.ext
  unfold operated
  rw [Equiv.apply_symm_apply]
  change (actual C (0 : Cot e →ₗ[R] M)).1 * (actual C v).1 = (actual C v).1
  rw [chart_zero, one_mul]

/-- Two projections of the universal M×M square-zero test force the value
of the derivative of the group multiplication on that test. Addition M×M→M
then gives the correct derivative on the same chart, including over rings
of characteristic 2. -/
theorem operated_add {M : Type u} [AddCommGroup M] [Module R M]
    (v w : Cot e →ₗ[R] M) : operated C v w = v + w := by
  let a := (LinearMap.inl R M M).comp v
  let b := (LinearMap.inr R M M).comp w
  let p := LinearMap.fst R M M
  let q := LinearMap.snd R M M
  let z := operated C a b
  have hp : p.comp z = v := by
    dsimp only [z]
    rw [operated_natural]
    have h₁ : p.comp a = v := by ext; rfl
    have h₂ : p.comp b = 0 := by ext; rfl
    rw [h₁, h₂, operated_left]
  have hq : q.comp z = w := by
    dsimp only [z]
    rw [operated_natural]
    have h₁ : q.comp a = 0 := by ext; rfl
    have h₂ : q.comp b = w := by ext; rfl
    rw [h₁, h₂, operated_right]
  have ha : (p + q).comp a = v := by ext x; simp [p, q, a]
  have hb : (p + q).comp b = w := by ext x; simp [p, q, b]
  have h := operated_natural C (p + q) a b
  change (p + q).comp z = operated C ((p + q).comp a) ((p + q).comp b) at h
  rw [ha, hb] at h
  calc
    operated C v w = (p + q).comp z := h.symm
    _ = p.comp z + q.comp z := by ext x; rfl
    _ = v + w := by rw [hp, hq]

/-- Actual maps act on the correctly marked group before any coordinate read. -/
def post {M : Type u} [AddCommGroup M] [Module R M]
    (f : A ⟶ A) [IsMonHom f] (v : ActualBased (A := A) M) : ActualBased (A := A) M :=
  ⟨v.1 ≫ f, by
    rw [Over.comp_left, ← Category.assoc, v.2]
    exact congrArg Over.Hom.left (IsMonHom.one_hom f)⟩

def derivativeRead {M : Type u} [AddCommGroup M] [Module R M]
    (f : A ⟶ A) [IsMonHom f] (v : Cot e →ₗ[R] M) : Cot e →ₗ[R] M :=
  (actual C).symm (post f (actual C v))

private theorem post_product {M : Type u} [AddCommGroup M] [Module R M]
    (f : A ⟶ A) [IsMonHom f] (x y : ActualBased (A := A) M) :
    post f (mul x y) = mul (post f x) (post f y) := by
  apply Subtype.ext
  exact MonObj.mul_comp x.1 y.1 f

theorem derivative_add_points {M : Type u} [AddCommGroup M] [Module R M]
    (f : A ⟶ A) [IsMonHom f] (v w : Cot e →ₗ[R] M) :
    derivativeRead C f (v + w) = derivativeRead C f v + derivativeRead C f w := by
  rw [← operated_add C v w,
    ← operated_add C (derivativeRead C f v) (derivativeRead C f w)]
  apply (actual C).injective
  unfold derivativeRead operated
  simp only [Equiv.apply_symm_apply, post_product]

theorem derivative_module_natural {M N : Type u} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (l : M →ₗ[R] N)
    (f : A ⟶ A) [IsMonHom f] (v : Cot e →ₗ[R] M) :
    l.comp (derivativeRead C f v) = derivativeRead C f (l.comp v) := by
  apply (actual C).injective
  rw [← chart_natural]
  unfold derivativeRead
  simp only [Equiv.apply_symm_apply]
  rw [← chart_natural]
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

/-- The derivative of the true based group map on the exact dual conormal. -/
def derivative (f : A ⟶ A) [IsMonHom f] :
    Module.Dual R (Cot e) →ₗ[R] Module.Dual R (Cot e) where
  toFun := derivativeRead C f
  map_add' := derivative_add_points C f
  map_smul' r v := by
    let l := r • (LinearMap.id : R →ₗ[R] R)
    have h (w : Cot e →ₗ[R] R) : l.comp w = r • w := by ext; rfl
    simpa only [h] using (derivative_module_natural C l f v).symm

theorem derivative_zero [IsMonHom (1 : A ⟶ A)] :
    derivative C (1 : A ⟶ A) = 0 := by
  apply LinearMap.ext
  intro v
  change derivativeRead C (1 : A ⟶ A) v = 0
  apply (actual C).injective
  simp only [derivativeRead, Equiv.apply_symm_apply]
  apply Subtype.ext
  change (actual C v).1 ≫ (1 : A ⟶ A) = (actual C (0 : Cot e →ₗ[R] R)).1
  rw [MonObj.comp_one, chart_zero]

theorem derivative_id : derivative C (𝟙 A) = LinearMap.id := by
  ext v
  change derivativeRead C (𝟙 A) v = v
  apply (actual C).injective
  simp only [derivativeRead, Equiv.apply_symm_apply]
  apply Subtype.ext
  exact Category.comp_id _

theorem derivative_comp (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] :
    derivative C (f ≫ g) = (derivative C g).comp (derivative C f) := by
  apply LinearMap.ext
  intro v
  change derivativeRead C (f ≫ g) v = derivativeRead C g (derivativeRead C f v)
  apply (actual C).injective
  simp only [derivativeRead, Equiv.apply_symm_apply]
  apply Subtype.ext
  exact (Category.assoc _ _ _).symm

theorem derivative_sum (f g : A ⟶ A) [IsMonHom f] [IsMonHom g] [IsMonHom (f * g)] :
    derivative C (f * g) = derivative C f + derivative C g := by
  apply LinearMap.ext
  intro v
  change derivativeRead C (f * g) v = derivativeRead C f v + derivativeRead C g v
  rw [← operated_add C]
  apply (actual C).injective
  simp only [derivativeRead, operated, Equiv.apply_symm_apply]
  apply Subtype.ext
  exact MonObj.comp_mul (actual C v).1 f g

end OriginalActualOriginLieAddition318

#print axioms OriginalActualOriginLieAddition318.chart_natural
#print axioms OriginalActualOriginLieAddition318.operated_add
#print axioms OriginalActualOriginLieAddition318.derivative_comp
#print axioms OriginalActualOriginLieAddition318.derivative_sum
#print axioms OriginalActualOriginLieAddition318.derivative_zero
