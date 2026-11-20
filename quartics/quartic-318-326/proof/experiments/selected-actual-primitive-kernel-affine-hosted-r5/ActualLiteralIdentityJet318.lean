module
public import ActualInfinitySquareZero318
public import SelectedLiteralTorsionKernel318
public import InfinityBoundaryScheme318
public import AffineProductEvaluation318
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
import all LiteralSchemePointGroup318
import all WeierstrassGluing318
public section
noncomputable section

namespace ActualLiteralIdentityJet318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ActualInfinitySquareZero318

universe u
variable {R M M' : Type u} [CommRing R]
variable [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
variable [AddCommGroup M'] [Module R M'] [Module Rᵐᵒᵖ M'] [IsCentralScalar R M']

abbrev test (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] := Spec (CommRingCat.of (S R M))

@[expose] def augmentation (R M : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [Module Rᵐᵒᵖ M] [IsCentralScalar R M] : Spec (CommRingCat.of R) ⟶ test R M :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R M).toRingHom)

@[expose] def testMap (l : M →ₗ[R] M') : test R M' ⟶ test R M :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map l).toRingHom)

@[expose] def geomJet (A B : R) (m : M) : test R M ⟶ WeierstrassGluing318.scheme A B :=
  InfinityBoundaryScheme318.point A B (jet A B m)

theorem geomJet_over (A B : R) (m : M) :
    geomJet A B m ≫ WeierstrassGluing318.structureMap A B = Spec.algebraMap R (S R M) :=
  InfinityBoundaryScheme318.point_over_base A B (jet A B m)

@[simp] theorem geomJet_zero (A B : R) :
    geomJet A B (0 : M) = Spec.algebraMap R (S R M) ≫ WeierstrassGluing318.infinity A B := by
  rw [geomJet, jet_zero] <;> exact InfinityBoundaryScheme318.point_origin A B

theorem geomJet_injective (A B : R) : Function.Injective (geomJet A B (M := M)) := by
  intro a b h
  exact jet_injective A B (ChartInputEquality318.infinity_injective A B (jet A B a) (jet A B b) h)

private theorem chart_precomp {D : Type u} [CommRing D] [Algebra R D]
    (A B : R) (f : InfinityChart318.Ring A B →ₐ[R] S R M) (g : S R M →ₐ[R] D) :
    Spec.map (CommRingCat.ofHom g.toRingHom) ≫ InfinityBoundaryScheme318.point A B f =
      InfinityBoundaryScheme318.point A B (g.comp f) := by
  unfold InfinityBoundaryScheme318.point InfinityBoundaryScheme318.chartPoint
  rw [← Category.assoc, ← Spec.map_comp] <;> rfl

@[simp] theorem augmentation_geomJet (A B : R) (m : M) :
    augmentation R M ≫ geomJet A B m = WeierstrassGluing318.infinity A B := by
  rw [augmentation, geomJet, chart_precomp, augmentation_jet] <;> rfl

@[reassoc] theorem geomJet_map (A B : R) (l : M →ₗ[R] M') (m : M) :
    testMap l ≫ geomJet A B m = geomJet A B (l m) := by
  rw [testMap, geomJet, chart_precomp, map_jet] <;> rfl

/-- The square-zero augmentation covers the entire underlying topological
space, even for a non-field base. It does not identify Scheme maps. -/
lemma augmentation_surjective : Function.Surjective (augmentation R M) := by
  let f : S R M →+* R := (TrivSqZeroExt.fstHom R R M).toRingHom
  have hs : Function.Surjective f := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  intro x
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker f : Set (S R M)) := by
    change (RingHom.ker f : Set (S R M)) ⊆ (x.asIdeal : Set (S R M))
    intro a ha
    have h0 : a.fst = 0 := RingHom.mem_ker.mp ha
    have he : a = TrivSqZeroExt.inr a.snd := TrivSqZeroExt.ext h0 rfl
    refine x.2.mem_of_pow_mem 2 ?_
    rw [he, pow_two, TrivSqZeroExt.inr_mul_inr]
    exact x.asIdeal.zero_mem
  rw [← _root_.range_comap_of_surjective R f hs] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  change PrimeSpectrum.comap f y = x
  exact hy

/-- Actual factorization through the Y=1 chart and classification of every
completed pointed map on the first-order test, not just constructed lifts. -/
theorem exists_geomJet (A B : R) (p : test R M ⟶ WeierstrassGluing318.scheme A B)
    (hbase : p ≫ WeierstrassGluing318.structureMap A B = Spec.algebraMap R (S R M))
    (h0 : augmentation R M ≫ p = WeierstrassGluing318.infinity A B) :
    ∃ m : M, p = geomJet A B m := by
  let j := WeierstrassGluing318.infinityChart A B
  have hmem : Set.range p ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (augmentation_surjective (R := R) (M := M)) x
    refine ⟨InfinitySmooth318.infinity A B y, ?_⟩
    simpa only [WeierstrassGluing318.infinity, Scheme.Hom.comp_apply] using
      (congrArg (fun f : Spec (CommRingCat.of R) ⟶ WeierstrassGluing318.scheme A B => f y) h0).symm
  let q := IsOpenImmersion.lift j p hmem
  have hq : q ≫ j = p := IsOpenImmersion.lift_fac _ _ _
  have hqb : q ≫ Spec.algebraMap R (InfinityChart318.Ring A B) = Spec.algebraMap R (S R M) := by
    change q ≫ InfinitySmooth318.structureMap A B = _
    rw [← WeierstrassGluing318.infinityChart_structure A B, ← Category.assoc, hq, hbase]
  let f := AffineProductEvaluation318.toAlgHom q hqb
  have hpf : InfinityBoundaryScheme318.point A B f = p := by
    unfold InfinityBoundaryScheme318.point InfinityBoundaryScheme318.chartPoint
    rw [AffineProductEvaluation318.map_toAlgHom q hqb]
    exact hq
  have hf : (TrivSqZeroExt.fstHom R R M).comp f = InfinityChart318.origin A B := by
    apply ChartInputEquality318.infinity_injective A B
    change InfinityBoundaryScheme318.point A B ((TrivSqZeroExt.fstHom R R M).comp f) =
      WeierstrassGluing318.infinity A B
    rw [← chart_precomp, hpf]
    exact h0
  exact ⟨(f (InfinityChart318.x A B)).snd, hpf.symm.trans (by
    rw [geomJet, ← eq_jet_of_augmentation A B f hf])⟩

section Literal
open SelectedLiteralTorsionKernel318 LiteralSchemePointOperations318

abbrev literalBase (n : ℕ) (V : Type) [AddCommGroup V]
    [Module (OpenJModel318.Base n) V] [Module (OpenJModel318.Base n)ᵐᵒᵖ V]
    [IsCentralScalar (OpenJModel318.Base n) V] : test (OpenJModel318.Base n) V ⟶ Base n :=
  Spec.algebraMap (OpenJModel318.Base n) (S (OpenJModel318.Base n) V)

@[expose] def literalJet (n : ℕ) {V : Type} [AddCommGroup V]
    [Module (OpenJModel318.Base n) V] [Module (OpenJModel318.Base n)ᵐᵒᵖ V]
    [IsCentralScalar (OpenJModel318.Base n) V] (v : V) : Points n (literalBase n V) :=
  ⟨geomJet (OpenJAffineScheme318.A n) (OpenJAffineScheme318.B n) v,
    geomJet_over (OpenJAffineScheme318.A n) (OpenJAffineScheme318.B n) v⟩

local notation "coeff" => OpenJModel318.Base
local notation "a4" => OpenJAffineScheme318.A
local notation "a6" => OpenJAffineScheme318.B
local notation "discUnit" => OpenJAffineScheme318.discriminant_unit

@[simp] theorem literalJet_zero (n : ℕ) {V : Type} [AddCommGroup V]
    [Module (OpenJModel318.Base n) V] [Module (OpenJModel318.Base n)ᵐᵒᵖ V]
    [IsCentralScalar (OpenJModel318.Base n) V] :
    literalJet n (V := V) (0 : V) = (0 : Points n (literalBase n V)) := by
  apply Subtype.ext
  exact geomJet_zero (a4 n) (a6 n)

private theorem sum_pull_val (n : ℕ) {T U : Scheme} (t : U ⟶ T) {b : T ⟶ Base n} {c : U ⟶ Base n}
    (p q : Points n b) (p' q' : Points n c)
    (hp : t ≫ p.val = p'.val) (hq : t ≫ q.val = q'.val) :
    t ≫ (p + q).val = (p' + q').val := by
  have H : t ≫ pair n b p q = pair n c p' q' := by
    apply pullback.hom_ext <;> simp only [Category.assoc, pair_fst, pair_snd, hp, hq]
  change t ≫ (pair n b p q ≫ CompletedAddition318.addition (a4 n) (a6 n) (discUnit n)) =
    pair n c p' q' ≫ CompletedAddition318.addition (a4 n) (a6 n) (discUnit n)
  rw [← Category.assoc, H]

/-- The actual completed addition has sum as its differential at the
identity. The two axes are independent first-order directions; a fold
map, not a reduced/geometric point check, now gives the diagonal sum. -/
theorem literalJet_add (n : ℕ) {V : Type} [AddCommGroup V]
    [Module (OpenJModel318.Base n) V] [Module (OpenJModel318.Base n)ᵐᵒᵖ V]
    [IsCentralScalar (OpenJModel318.Base n) V] (a b : V) :
    literalJet n (V := V) (a + b) = literalJet n (V := V) a + literalJet n (V := V) b := by
  let p := literalJet n (V := V × V) (a, (0 : V))
  let q := literalJet n (V := V × V) ((0 : V), b)
  let P := p + q
  have h0 : augmentation (coeff n) (V × V) ≫ P.val = origin n := by
    have H := sum_pull_val n (augmentation (coeff n) (V × V)) p q
      (0 : Points n (𝟙 (Base n))) 0
      (by change _ = (𝟙 (Base n)) ≫ origin n; rw [Category.id_comp]; exact augmentation_geomJet (a4 n) (a6 n) _)
      (by change _ = (𝟙 (Base n)) ≫ origin n; rw [Category.id_comp]; exact augmentation_geomJet (a4 n) (a6 n) _)
    rw [add_zero] at H
    exact H.trans (Category.id_comp _)
  obtain ⟨z, hz⟩ := exists_geomJet (M := V × V) (a4 n) (a6 n) P.val P.property h0
  let f₁ : V × V →ₗ[coeff n] V := LinearMap.fst (coeff n) V V
  let f₂ : V × V →ₗ[coeff n] V := LinearMap.snd (coeff n) V V
  have hf₁ : f₁ z = a := by
    apply geomJet_injective (M := V) (a4 n) (a6 n)
    rw [← geomJet_map (a4 n) (a6 n) f₁ z, ← hz]
    have H := sum_pull_val n (testMap f₁) p q (literalJet n a) (literalJet n (0 : V))
      (geomJet_map (a4 n) (a6 n) f₁ _) (geomJet_map (a4 n) (a6 n) f₁ _)
    simpa only [literalJet_zero, add_zero] using H
  have hf₂ : f₂ z = b := by
    apply geomJet_injective (M := V) (a4 n) (a6 n)
    rw [← geomJet_map (a4 n) (a6 n) f₂ z, ← hz]
    have H := sum_pull_val n (testMap f₂) p q (literalJet n (0 : V)) (literalJet n b)
      (geomJet_map (a4 n) (a6 n) f₂ _) (geomJet_map (a4 n) (a6 n) f₂ _)
    simpa only [literalJet_zero, zero_add] using H
  have hz' : z = (a, b) := Prod.ext hf₁ hf₂
  let F : V × V →ₗ[coeff n] V := (LinearMap.id : V →ₗ[coeff n] V).coprod LinearMap.id
  have hFa : F (a, 0) = a := add_zero a
  have hFb : F (0, b) = b := zero_add b
  have hFab : F (a,b) = a+b := rfl
  apply Subtype.ext
  calc
    (literalJet n (a+b)).val = testMap F ≫ geomJet (a4 n) (a6 n) (a,b) := by
      rw [geomJet_map, hFab] <;> rfl
    _ = testMap F ≫ P.val := by rw [hz, hz']
    _ = (literalJet n a + literalJet n b).val := by
      apply sum_pull_val n _ p q
      · simpa only [hFa] using geomJet_map (a4 n) (a6 n) F (a, (0 : V))
      · simpa only [hFb] using geomJet_map (a4 n) (a6 n) F ((0 : V), b)

/-- The genuine multiplication morphism acts on all identity square-zero
directions by m, with no assumption on finite or étale kernels. -/
theorem literalJet_mul (n : ℕ) {V : Type} [AddCommGroup V]
    [Module (OpenJModel318.Base n) V] [Module (OpenJModel318.Base n)ᵐᵒᵖ V]
    [IsCentralScalar (OpenJModel318.Base n) V] (m : ℕ) (a : V) :
    (literalJet n (V := V) a).val ≫ mulMap n m = (literalJet n (V := V) (m • a)).val := by
  let L : V →+ Points n (literalBase n V) :=
    { toFun := literalJet n (V := V)
      map_zero' := literalJet_zero n (V := V)
      map_add' := literalJet_add n (V := V) }
  have h := congrArg Subtype.val (map_nsmul L m a)
  exact (mul_value n m (literalBase n V) (literalJet n a)).symm.trans h.symm
end Literal

end ActualLiteralIdentityJet318
