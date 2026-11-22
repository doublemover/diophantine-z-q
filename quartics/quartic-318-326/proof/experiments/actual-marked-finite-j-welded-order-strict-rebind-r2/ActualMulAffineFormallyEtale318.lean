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

local notation "coeff" => OpenJModel318.Base

/-- Smoothness of the actual completed short curve restricts to the
specified affine open, not to an unrelated matrix model. -/
theorem chart_smooth (n : ℕ) {A : Type} [CommRing A] [Algebra (OpenJModel318.Base n) A]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (hi : i ≫ projection n = baseFor n A) : Algebra.Smooth (coeff n) A := by
  letI : Smooth (projection n) := WeierstrassGluing318.literal_smooth n
  have hs : Smooth (i ≫ projection n) := by infer_instance
  rw [hi] at hs
  exact RingHom.smooth_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap (coeff n) A))).mp hs)

private theorem comp_target (n : ℕ) {A B T : Type} [CommRing A] [CommRing B] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B]
    [Algebra (OpenJModel318.Base n) T] [Algebra B A] [Algebra B T]
    [IsScalarTower (OpenJModel318.Base n) B A] [IsScalarTower (OpenJModel318.Base n) B T] (a : A →ₐ[B] T) :
    (a.restrictScalars (coeff n)).comp (IsScalarTower.toAlgHom (coeff n) B A) =
      IsScalarTower.toAlgHom (coeff n) B T := by
  apply AlgHom.ext
  intro b
  exact a.commutes b

/-- Exact B-algebra lifting over the actual chosen target chart. A source
lift is produced by formal smoothness over the original coefficient ring, then corrected
by the non-split identity kernel. Its B-linearity is forced by the literal
target equality, not assumed of the smooth preliminary lift. -/
theorem squareZero_unique_lift (n : ℕ) {A B : Type} [CommRing A] [CommRing B]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B]
    [Algebra B A] [IsScalarTower (OpenJModel318.Base n) B A]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ Curve n) [IsOpenImmersion j]
    (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
    (m : ℕ) (h : i ≫ mulMap n m = specOf n (IsScalarTower.toAlgHom (coeff n) B A) ≫ j)
    (hm : IsUnit (m : (coeff n))) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T] [Algebra B T]
    [IsScalarTower (OpenJModel318.Base n) B T] (I : Ideal T) (hI : I ^ 2 = ⊥)
    (g : A →ₐ[B] (T ⧸ I)) :
    ∃! a : A →ₐ[B] T, (Ideal.Quotient.mkₐ B I).comp a = g := by
  letI : Algebra.Smooth (coeff n) A := chart_smooth n i hi
  letI : Algebra.FormallySmooth (coeff n) A := inferInstance
  let k := IsScalarTower.toAlgHom (coeff n) B A
  let β := IsScalarTower.toAlgHom (coeff n) B T
  let g₀ := g.restrictScalars (coeff n)
  let p₀ := eval n i hi g₀
  let q := eval n j hj β
  have hn : IsNilpotent I := ⟨2, hI⟩
  let f := Algebra.FormallySmooth.lift I hn g₀
  have hf : (Ideal.Quotient.mkₐ (coeff n) I).comp f = g₀ :=
    Algebra.FormallySmooth.comp_lift I hn g₀
  let p := eval n i hi f
  have hp : reduce n I p = p₀ := by
    change reduce n I (eval n i hi f) = eval n i hi g₀
    rw [eval_reduce, hf]
  have hβ : (Ideal.Quotient.mkₐ (coeff n) I).comp β = g₀.comp k := by
    apply AlgHom.ext
    intro b
    change algebraMap B (T ⧸ I) b = g (algebraMap B A b)
    exact (g.commutes b).symm
  have hq : reduce n I q = m • p₀ := by
    calc
      _ = eval n j hj ((Ideal.Quotient.mkₐ (coeff n) I).comp β) := eval_reduce n j hj I β
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
      commutes' := fun b => congrArg (fun f : B →ₐ[(coeff n)] T => f b) htarget }
  have hamod : (Ideal.Quotient.mkₐ (coeff n) I).comp a = g₀ := by
    apply eval_injective n i hi
    rw [← eval_reduce, ha]
    exact ht.1
  have hB : (Ideal.Quotient.mkₐ B I).comp aB = g := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun f : A →ₐ[(coeff n)] (T ⧸ I) => f x) hamod
  refine ⟨aB, hB, ?_⟩
  intro b hb
  let b₀ := b.restrictScalars (coeff n)
  have hbmod : (Ideal.Quotient.mkₐ (coeff n) I).comp b₀ = g₀ := by
    apply AlgHom.ext
    intro x
    exact congrArg (fun f : A →ₐ[B] (T ⧸ I) => f x) hb
  have hb₁ : reduce n I (eval n i hi b₀) = p₀ := by
    change reduce n I (eval n i hi b₀) = eval n i hi g₀
    rw [eval_reduce, hbmod]
  have hb₂ : m • eval n i hi b₀ = q := by
    rw [eval_mul n i j hi hj m k h b₀]
    change eval n j hj ((b.restrictScalars (coeff n)).comp (IsScalarTower.toAlgHom (coeff n) B A)) =
      eval n j hj (IsScalarTower.toAlgHom (coeff n) B T)
    rw [comp_target n b]
  have hba : b₀ = a := (eval_injective n i hi) ((huniq _ ⟨hb₁, hb₂⟩).trans ha.symm)
  apply AlgHom.ext
  intro x
  exact congrArg (fun f : A →ₐ[(coeff n)] T => f x) hba

/-- Actual affine restriction, formally étale over the genuine target
algebra. The test keeps B's prescribed map throughout. -/
theorem formallyEtale_of_actual_restriction (n : ℕ) {A B : Type} [CommRing A] [CommRing B]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B]
    [Algebra B A] [IsScalarTower (OpenJModel318.Base n) B A]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ Curve n) [IsOpenImmersion j]
    (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
    (m : ℕ) (h : i ≫ mulMap n m = specOf n (IsScalarTower.toAlgHom (coeff n) B A) ≫ j)
    (hm : IsUnit (m : (coeff n))) :
    Algebra.FormallyEtale B A := by
  apply Algebra.FormallyEtale.iff_comp_bijective.mpr
  intro T _ _ I hI
  letI : Algebra (coeff n) T := ((algebraMap B T).comp (algebraMap (coeff n) B)).toAlgebra
  letI : IsScalarTower (coeff n) B T := IsScalarTower.of_algebraMap_eq' rfl
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
theorem etale_of_actual_restriction (n : ℕ) {A B : Type} [CommRing A] [CommRing B]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B]
    [Algebra B A] [IsScalarTower (OpenJModel318.Base n) B A]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ Curve n) [IsOpenImmersion j]
    (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
    (m : ℕ) (h : i ≫ mulMap n m = specOf n (IsScalarTower.toAlgHom (coeff n) B A) ≫ j)
    [Algebra.FinitePresentation B A] (hm : IsUnit (m : (coeff n))) :
    Etale (Spec.algebraMap B A) := by
  let hEtale : Algebra.Etale B A :=
    ⟨formallyEtale_of_actual_restriction n i j hi hj m h hm, inferInstance⟩
  exact (HasRingHomProperty.Spec_iff (P := @Etale)
    (φ := CommRingCat.ofHom (algebraMap B A))).mpr (RingHom.etale_algebraMap.mpr hEtale)

/-- The exact restricted ring arrow can itself be obtained from actual
chart containment, without supplying a new algebra structure in advance. -/
theorem exists_formallyEtale_mul_restriction (n : ℕ) {A B : Type} [CommRing A] [CommRing B]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (j : Spec (CommRingCat.of B) ⟶ Curve n) [IsOpenImmersion j]
    (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
    (m : ℕ) (hm : IsUnit (m : (coeff n))) (hmem : Set.range (i ≫ mulMap n m) ⊆ Set.range j) :
    ∃ k : B →ₐ[(coeff n)] A, (i ≫ mulMap n m = specOf n k ≫ j) ∧ k.toRingHom.FormallyEtale := by
  obtain ⟨k, hk⟩ := exists_mul_restriction n i j hi hj m hmem
  letI : Algebra B A := k.toRingHom.toAlgebra
  letI : IsScalarTower (coeff n) B A := IsScalarTower.of_algHom k
  have he : IsScalarTower.toAlgHom (coeff n) B A = k := AlgHom.ext (fun _ => rfl)
  have h : i ≫ mulMap n m = specOf n (IsScalarTower.toAlgHom (coeff n) B A) ≫ j := by rw [he]; exact hk
  refine ⟨k, hk, ?_⟩
  exact formallyEtale_of_actual_restriction n i j hi hj m h hm

end ActualMulAffineFormallyEtale318
