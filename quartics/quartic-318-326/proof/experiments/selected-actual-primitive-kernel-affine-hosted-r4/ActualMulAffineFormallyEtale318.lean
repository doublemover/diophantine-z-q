module
public import ActualMulAffineCharts318
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Basic
import all WeierstrassGluing318
public section
noncomputable section

namespace ActualMulAffineFormallyEtale318
open AlgebraicGeometry CategoryTheory
open ActualNonSplitIdentityLifts318 ActualMulAffineCharts318
open SelectedLiteralTorsionKernel318 LiteralSchemePointOperations318

variable (n : ℕ)
local notation "R₀" => OpenJModel318.Base n
variable {A B : Type} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra R₀ B]

/-- Smoothness of the actual completed short curve restricts to the
specified affine open, not to an unrelated matrix model. -/
theorem chart_smooth (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (hi : i ≫ projection n = baseFor n A) : Algebra.Smooth R₀ A := by
  letI : Smooth (projection n) := WeierstrassGluing318.literal_smooth n
  have hs : Smooth (i ≫ projection n) := by infer_instance
  rw [hi] at hs
  exact RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap R₀ A))).mp hs)

section Tower

variable [Algebra B A] [IsScalarTower R₀ B A]
variable (i : Spec (CommRingCat.of A) ⟶ Curve n) [iOpen : IsOpenImmersion i]
variable (j : Spec (CommRingCat.of B) ⟶ Curve n) [jOpen : IsOpenImmersion j]
variable (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
variable (m : ℕ)
variable (h : i ≫ mulMap n m = specOf n (IsScalarTower.toAlgHom R₀ B A) ≫ j)

private theorem comp_target {T : Type} [CommRing T] [Algebra R₀ T] [Algebra B T]
    [IsScalarTower R₀ B T] (a : A →ₐ[B] T) :
    (a.restrictScalars R₀).comp (IsScalarTower.toAlgHom R₀ B A) =
      IsScalarTower.toAlgHom R₀ B T := by
  apply AlgHom.ext
  intro b
  exact a.commutes b

include iOpen jOpen hi hj h

/-- Exact B-algebra lifting over the actual chosen target chart. A source
lift is produced by formal smoothness over the original R₀, then corrected
by the non-split identity kernel. Its B-linearity is forced by the literal
target equality, not assumed of the smooth preliminary lift. -/
theorem squareZero_unique_lift
    (hm : IsUnit (m : R₀)) {T : Type} [CommRing T] [Algebra R₀ T] [Algebra B T]
    [IsScalarTower R₀ B T] (I : Ideal T) (hI : I ^ 2 = ⊥)
    (g : A →ₐ[B] (T ⧸ I)) :
    ∃! a : A →ₐ[B] T, (Ideal.Quotient.mkₐ B I).comp a = g := by
  letI : Algebra.Smooth R₀ A := chart_smooth n i hi
  letI : Algebra.FormallySmooth R₀ A := inferInstance
  let k := IsScalarTower.toAlgHom R₀ B A
  let β := IsScalarTower.toAlgHom R₀ B T
  let g₀ := g.restrictScalars R₀
  let p₀ := eval n i hi g₀
  let q := eval n j hj β
  have hn : IsNilpotent I := ⟨2, hI⟩
  let f := Algebra.FormallySmooth.lift I hn g₀
  have hf : (Ideal.Quotient.mkₐ R₀ I).comp f = g₀ :=
    Algebra.FormallySmooth.comp_lift I hn g₀
  let p := eval n i hi f
  have hp : reduce n I p = p₀ := by
    change reduce n I (eval n i hi f) = eval n i hi g₀
    rw [eval_reduce, hf]
  have hβ : (Ideal.Quotient.mkₐ R₀ I).comp β = g₀.comp k := by
    apply AlgHom.ext
    intro b
    change algebraMap B (T ⧸ I) b = g (algebraMap B A b)
    exact (g.commutes b).symm
  have hq : reduce n I q = m • p₀ := by
    calc
      _ = eval n j hj ((Ideal.Quotient.mkₐ R₀ I).comp β) := eval_reduce n j hj I β
      _ = eval n j hj (g₀.comp k) := congrArg (eval n j hj) hβ
      _ = _ := (eval_mul n i j hi hj m k h g₀).symm
  obtain ⟨t, ht, huniq⟩ := existsUnique_translated_lift n I hI m hm p₀ q p hp hq
  obtain ⟨a, ha⟩ := exists_eval_of_reduce n i hi I hI t g₀ ht.1
  have htarget : a.comp k = β := by
    apply eval_injective n j hj
    calc
      _ = m • eval n i hi a := (eval_mul n i j hi hj m k h a).symm
      _ = q := by rw [ha, ht.2]
      _ = _ := rfl
  let aB : A →ₐ[B] T :=
    { (a : A →+* T) with
      commutes' := fun b => congrArg (fun f : B →ₐ[R₀] T => f b) htarget }
  have hamod : (Ideal.Quotient.mkₐ R₀ I).comp a = g₀ := by
    apply eval_injective n i hi
    rw [← eval_reduce, ha]
    exact ht.1
  have hB : (Ideal.Quotient.mkₐ B I).comp aB = g := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun f : A →ₐ[R₀] (T ⧸ I) => f x) hamod
  refine ⟨aB, hB, ?_⟩
  intro b hb
  let b₀ := b.restrictScalars R₀
  have hbmod : (Ideal.Quotient.mkₐ R₀ I).comp b₀ = g₀ := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun f : A →ₐ[B] (T ⧸ I) => f x) hb
  have hb₁ : reduce n I (eval n i hi b₀) = p₀ := by
    change reduce n I (eval n i hi b₀) = eval n i hi g₀
    rw [eval_reduce, hbmod]
  have hb₂ : m • eval n i hi b₀ = q := by
    rw [eval_mul n i j hi hj m k h b₀]
    change eval n j hj ((b.restrictScalars R₀).comp (IsScalarTower.toAlgHom R₀ B A)) =
      eval n j hj (IsScalarTower.toAlgHom R₀ B T)
    rw [comp_target n b]
  have hba : b₀ = a := (eval_injective n i hi) ((huniq _ ⟨hb₁, hb₂⟩).trans ha.symm)
  apply AlgHom.ext
  intro x
  exact congrArg (fun f : A →ₐ[R₀] T => f x) hba

/-- Actual affine restriction, formally étale over the genuine target
algebra. The test keeps B's prescribed map throughout. -/
theorem formallyEtale_of_actual_restriction (hm : IsUnit (m : R₀)) :
    Algebra.FormallyEtale B A := by
  apply Algebra.FormallyEtale.iff_comp_bijective.mpr
  intro T _ _ I hI
  letI : Algebra R₀ T := ((algebraMap B T).comp (algebraMap R₀ B)).toAlgebra
  letI : IsScalarTower R₀ B T := IsScalarTower.of_algebraMap_eq' rfl
  constructor
  · intro a b hab
    obtain ⟨c, _, hu⟩ := squareZero_unique_lift n i j hi hj m h hm I hI
      ((Ideal.Quotient.mkₐ B I).comp a)
    exact (hu a rfl).trans (hu b hab.symm).symm
  · intro g
    obtain ⟨a, ha, _⟩ := squareZero_unique_lift n i j hi hj m h hm I hI g
    exact ⟨a, ha⟩

/-- This is a local affine conclusion only; relative finite presentation
is kept visible rather than promoted to a global finite-étale assertion. -/
theorem etale_of_actual_restriction [Algebra.FinitePresentation B A] (hm : IsUnit (m : R₀)) :
    Etale (Spec.algebraMap B A) := by
  let hEtale : Algebra.Etale B A :=
    ⟨formallyEtale_of_actual_restriction n i j hi hj m h hm, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap B A))).mpr (RingHom.etale_algebraMap.mpr hEtale)

end Tower

/-- The exact restricted ring arrow can itself be obtained from actual
chart containment, without supplying a new algebra structure in advance. -/
theorem exists_formallyEtale_mul_restriction
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ Curve n) [IsOpenImmersion j]
    (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
    (m : ℕ) (hm : IsUnit (m : R₀)) (hmem : Set.range (i ≫ mulMap n m) ⊆ Set.range j) :
    ∃ k : B →ₐ[R₀] A, (i ≫ mulMap n m = specOf n k ≫ j) ∧ k.toRingHom.FormallyEtale := by
  obtain ⟨k, hk⟩ := exists_mul_restriction n i j hi hj m hmem
  letI : Algebra B A := k.toRingHom.toAlgebra
  letI : IsScalarTower R₀ B A := IsScalarTower.of_algHom k
  have he : IsScalarTower.toAlgHom R₀ B A = k := AlgHom.ext (fun _ => rfl)
  have h : i ≫ mulMap n m = specOf n (IsScalarTower.toAlgHom R₀ B A) ≫ j := by rw [he]; exact hk
  refine ⟨k, hk, ?_⟩
  exact formallyEtale_of_actual_restriction n i j hi hj m h hm

end ActualMulAffineFormallyEtale318
