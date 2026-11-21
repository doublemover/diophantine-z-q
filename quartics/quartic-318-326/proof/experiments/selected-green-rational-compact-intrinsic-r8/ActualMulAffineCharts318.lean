module
public import ActualNonSplitIdentityLifts318
import all WeierstrassGluing318
public section
noncomputable section

namespace ActualMulAffineCharts318
open AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 LiteralSchemePointOperations318
open ActualNonSplitIdentityLifts318

local notation "coeff" => OpenJModel318.Base

theorem spec_of_comp (n : ℕ) {A B T : Type} [CommRing A] [CommRing B] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B] [Algebra (OpenJModel318.Base n) T]
    (g : B →ₐ[(coeff n)] T) (f : A →ₐ[(coeff n)] B) :
    specOf n g ≫ specOf n f = specOf n (g.comp f) := by
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫
    Spec.map (CommRingCat.ofHom f.toRingHom) = _
  rw [← Spec.map_comp] <;> rfl

theorem spec_of_base (n : ℕ) {A T : Type} [CommRing A] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) T]
    (f : A →ₐ[(coeff n)] T) : specOf n f ≫ baseFor n A = baseFor n T := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (coeff n) A)) = Spec.map (CommRingCat.ofHom (algebraMap (coeff n) T))
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext f.comp_algebraMap

/-- A literal evaluation on a specified affine chart of the original
completed curve. The coefficient map and chart both remain visible. -/
@[expose] def eval (n : ℕ) {A T : Type} [CommRing A] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) T]
    (i : Spec (CommRingCat.of A) ⟶ Curve n)
    (hi : i ≫ projection n = baseFor n A) (f : A →ₐ[(coeff n)] T) : pointsFor n T :=
  ⟨specOf n f ≫ i, by rw [Category.assoc, hi, spec_of_base]⟩

theorem eval_injective (n : ℕ) {A T : Type} [CommRing A] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) T]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (hi : i ≫ projection n = baseFor n A) :
    Function.Injective (eval n i hi : (A →ₐ[(coeff n)] T) → pointsFor n T) := by
  intro f g h
  have hv := congrArg Subtype.val h
  change specOf n f ≫ i = specOf n g ≫ i at hv
  have H := Spec.map_injective ((cancel_mono i).mp hv)
  apply AlgHom.ext
  intro x
  exact congrArg (fun k : CommRingCat.of A ⟶ CommRingCat.of T => k.hom x) H

theorem eval_reduce (n : ℕ) {A T : Type} [CommRing A] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) T]
    (i : Spec (CommRingCat.of A) ⟶ Curve n)
    (hi : i ≫ projection n = baseFor n A) (I : Ideal T) (f : A →ₐ[(coeff n)] T) :
    reduce n I (eval n i hi f) = eval n i hi ((Ideal.Quotient.mkₐ (coeff n) I).comp f) := by
  apply Subtype.ext
  change (pullPoint n (Ideal.Quotient.mkₐ (coeff n) I) (eval n i hi f)).val = _
  rw [pullPoint_val]
  change specOf n (Ideal.Quotient.mkₐ (coeff n) I) ≫ (specOf n f ≫ i) =
    specOf n ((Ideal.Quotient.mkₐ (coeff n) I).comp f) ≫ i
  rw [← Category.assoc, spec_of_comp]

/-- Extract the real affine algebra map from a point whose image is in
the actual open chart. No coordinates are selected by arithmetic. -/
theorem exists_eval (n : ℕ) {A T : Type} [CommRing A] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) T]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (hi : i ≫ projection n = baseFor n A) (p : pointsFor n T)
    (h : Set.range p.val ⊆ Set.range i) : ∃ f : A →ₐ[(coeff n)] T, eval n i hi f = p := by
  let p' := IsOpenImmersion.lift i p.val h
  have hfac : p' ≫ i = p.val := IsOpenImmersion.lift_fac _ _ _
  have hp' : p' ≫ baseFor n A = baseFor n T := by
    rw [← hi, ← Category.assoc, hfac]
    exact p.property
  let f := AffineProductEvaluation318.toAlgHom p' hp'
  refine ⟨f, Subtype.ext ?_⟩
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ i = p.val
  rw [AffineProductEvaluation318.map_toAlgHom p' hp', hfac]

/-- An open-chart factorization of the reduction forces the actual lift
to factor through that same chart: the quotient ideal is square-zero. -/
theorem exists_eval_of_reduce (n : ℕ) {A T : Type} [CommRing A] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) T]
    (i : Spec (CommRingCat.of A) ⟶ Curve n) [IsOpenImmersion i]
    (hi : i ≫ projection n = baseFor n A) (I : Ideal T) (hI : I ^ 2 = ⊥)
    (p : pointsFor n T) (f₀ : A →ₐ[(coeff n)] (T ⧸ I))
    (h : reduce n I p = eval n i hi f₀) : ∃ f : A →ₐ[(coeff n)] T, eval n i hi f = p := by
  let q := specOf n (Ideal.Quotient.mkₐ (coeff n) I)
  have hs : Function.Surjective q := by
    intro x
    have hx : x ∈ PrimeSpectrum.zeroLocus (I : Set T) := by
      change (I : Set T) ⊆ (x.asIdeal : Set T)
      intro a ha
      apply x.2.mem_of_pow_mem 2
      rw [pow_two, ActualNonSplitIdealChart318.mul_zero_of_mem I hI ha ha]
      exact x.asIdeal.zero_mem
    have he := _root_.range_comap_of_surjective (T ⧸ I) (Ideal.Quotient.mk I)
      (Ideal.Quotient.mk_surjective (I := I))
    rw [Ideal.mk_ker] at he
    rw [← he] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy⟩
  apply exists_eval n i hi p
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hs x
  rw [← hy]
  have hh := congrArg Subtype.val h
  change (pullPoint n (Ideal.Quotient.mkₐ (coeff n) I) p).val = specOf n f₀ ≫ i at hh
  rw [pullPoint_val] at hh
  exact ⟨specOf n f₀ y,
    (congrArg (fun k : Spec (CommRingCat.of (T ⧸ I)) ⟶ Curve n => k y) hh).symm⟩

/-- The affine ring arrow is extracted from the literal multiplication
morphism between the specified actual chart images. -/
theorem exists_mul_restriction (n : ℕ) {A B : Type} [CommRing A] [CommRing B]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B]
    (i : Spec (CommRingCat.of A) ⟶ Curve n)
    (j : Spec (CommRingCat.of B) ⟶ Curve n) [IsOpenImmersion j]
    (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
    (m : ℕ) (h : Set.range (i ≫ mulMap n m) ⊆ Set.range j) :
    ∃ k : B →ₐ[(coeff n)] A, i ≫ mulMap n m = specOf n k ≫ j := by
  let f := IsOpenImmersion.lift j (i ≫ mulMap n m) h
  have hf : f ≫ j = i ≫ mulMap n m := IsOpenImmersion.lift_fac _ _ _
  have hfb : f ≫ baseFor n B = baseFor n A := by
    rw [← hj, ← Category.assoc, hf, Category.assoc, mul_over, hi]
  let k := AffineProductEvaluation318.toAlgHom f hfb
  refine ⟨k, ?_⟩
  change _ = Spec.map (CommRingCat.ofHom k.toRingHom) ≫ j
  rw [AffineProductEvaluation318.map_toAlgHom f hfb, hf]

/-- Compatibility of actual [m] with evaluating this exact chart
restriction, for every coefficient algebra. -/
theorem eval_mul (n : ℕ) {A B T : Type} [CommRing A] [CommRing B] [CommRing T]
    [Algebra (OpenJModel318.Base n) A] [Algebra (OpenJModel318.Base n) B] [Algebra (OpenJModel318.Base n) T]
    (i : Spec (CommRingCat.of A) ⟶ Curve n)
    (j : Spec (CommRingCat.of B) ⟶ Curve n)
    (hi : i ≫ projection n = baseFor n A) (hj : j ≫ projection n = baseFor n B)
    (m : ℕ) (k : B →ₐ[(coeff n)] A) (h : i ≫ mulMap n m = specOf n k ≫ j)
    (f : A →ₐ[(coeff n)] T) :
    m • eval n i hi f = eval n j hj (f.comp k) := by
  apply Subtype.ext
  rw [mul_value n m (baseFor n T) (eval n i hi f)]
  change (specOf n f ≫ i) ≫ mulMap n m = specOf n (f.comp k) ≫ j
  rw [Category.assoc, h, ← Category.assoc, spec_of_comp]

end ActualMulAffineCharts318
