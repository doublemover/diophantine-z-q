module
public import ActualNonSplitIdealChart318
public import ActualLiteralIdentityJet318
public import Mathlib.Tactic.Abel
import all LiteralSchemePointGroup318
import all WeierstrassGluing318
public section
noncomputable section

namespace ActualNonSplitIdentityLifts318
open AlgebraicGeometry CategoryTheory
open SelectedLiteralTorsionKernel318 LiteralSchemePointOperations318
open ActualLiteralIdentityJet318 ActualNonSplitIdealChart318

local notation "coeff" => OpenJModel318.Base
local notation "a4" => OpenJAffineScheme318.A
local notation "a6" => OpenJAffineScheme318.B

abbrev baseFor (n : ℕ) (T : Type) [CommRing T] [Algebra (OpenJModel318.Base n) T] :
    Spec (CommRingCat.of T) ⟶ Base n :=
  Spec.algebraMap (coeff n) T

abbrev pointsFor (n : ℕ) (T : Type) [CommRing T] [Algebra (OpenJModel318.Base n) T] :=
  Points n (baseFor n T)

abbrev specOf (n : ℕ) {T D : Type} [CommRing T] [CommRing D]
    [Algebra (OpenJModel318.Base n) T] [Algebra (OpenJModel318.Base n) D]
    (f : T →ₐ[coeff n] D) : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of T) :=
  Spec.map (CommRingCat.ofHom f.toRingHom)

private theorem spec_over (n : ℕ) {T D : Type} [CommRing T] [CommRing D]
    [Algebra (OpenJModel318.Base n) T] [Algebra (OpenJModel318.Base n) D]
    (f : T →ₐ[coeff n] D) : specOf n f ≫ baseFor n T = baseFor n D := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (coeff n) T)) =
    Spec.map (CommRingCat.ofHom (algebraMap (coeff n) D))
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext f.comp_algebraMap

private def pullOver (n : ℕ) {U V : Scheme} (b : U ⟶ Base n) (c : V ⟶ Base n)
    (f : V ⟶ U) (h : f ≫ b = c) : Points n b →+ Points n c := by
  subst c
  exact precomp n b f

private theorem pullOver_val (n : ℕ) {U V : Scheme} (b : U ⟶ Base n) (c : V ⟶ Base n)
    (f : V ⟶ U) (h : f ≫ b = c) (p : Points n b) :
    (pullOver n b c f h p).val = f ≫ p.val := by
  subst c
  exact precomp_val n b f p

/-- Actual functorial precomposition over the same literal base. -/
def pullPoint (n : ℕ) {T D : Type} [CommRing T] [CommRing D]
    [Algebra (OpenJModel318.Base n) T] [Algebra (OpenJModel318.Base n) D]
    (f : T →ₐ[coeff n] D) : pointsFor n T →+ pointsFor n D :=
  pullOver n (baseFor n T) (baseFor n D) (specOf n f) (spec_over n f)

@[simp] theorem pullPoint_val (n : ℕ) {T D : Type} [CommRing T] [CommRing D]
    [Algebra (OpenJModel318.Base n) T] [Algebra (OpenJModel318.Base n) D]
    (f : T →ₐ[coeff n] D) (p : pointsFor n T) :
    (pullPoint n f p).val = specOf n f ≫ p.val := pullOver_val n _ _ _ _ p

abbrev reduce (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) : pointsFor n T →+ pointsFor n (T ⧸ I) :=
  pullPoint n (Ideal.Quotient.mkₐ (coeff n) I)

private theorem point_map (n : ℕ) {T D : Type} [CommRing T] [CommRing D]
    [Algebra (OpenJModel318.Base n) T] [Algebra (OpenJModel318.Base n) D]
    (f : InfinityChart318.Ring (a4 n) (a6 n) →ₐ[coeff n] T) (g : T →ₐ[coeff n] D) :
    specOf n g ≫ InfinityBoundaryScheme318.point (a4 n) (a6 n) f =
      InfinityBoundaryScheme318.point (a4 n) (a6 n) (g.comp f) := by
  unfold specOf InfinityBoundaryScheme318.point InfinityBoundaryScheme318.chartPoint
  rw [← Category.assoc, ← Spec.map_comp] <;> rfl

private theorem quotient_surjective (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Function.Surjective (specOf n (Ideal.Quotient.mkₐ (coeff n) I)) := by
  let f : T →+* T ⧸ I := Ideal.Quotient.mk I
  have hs : Function.Surjective f := Ideal.Quotient.mk_surjective
  intro x
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker f : Set T) := by
    change (RingHom.ker f : Set T) ⊆ (x.asIdeal : Set T)
    intro a ha
    have hmem : a ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp ha)
    apply x.2.mem_of_pow_mem 2
    rw [pow_two, mul_zero_of_mem I hI hmem hmem]
    exact x.asIdeal.zero_mem
  rw [← _root_.range_comap_of_surjective (T ⧸ I) f hs] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  change PrimeSpectrum.comap f y = x
  exact hy

/-- Actual pointed ideal directions, constructed only by the canonical
split specimen map; the coefficient quotient need not split. -/
@[expose] def idealJet (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Direction (coeff n) I →+ pointsFor n T :=
  (pullPoint n (specimen (coeff n) I hI)).comp
    { toFun := literalJet n
      map_zero' := literalJet_zero n
      map_add' := literalJet_add n }

@[reassoc] theorem idealJet_val (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction (coeff n) I) :
    (idealJet n I hI a).val =
      InfinityBoundaryScheme318.point (a4 n) (a6 n) (idealChart (coeff n) (a4 n) (a6 n) I hI a) := by
  change (pullPoint n (specimen (coeff n) I hI) (literalJet n a)).val = _
  rw [pullPoint_val]
  exact point_map n (ActualInfinitySquareZero318.jet (a4 n) (a6 n) a) (specimen (coeff n) I hI)

theorem idealJet_reduce (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction (coeff n) I) :
    reduce n I (idealJet n I hI a) = 0 := by
  apply Subtype.ext
  change (pullPoint n (Ideal.Quotient.mkₐ (coeff n) I) (idealJet n I hI a)).val =
    baseFor n (T ⧸ I) ≫ origin n
  rw [pullPoint_val, idealJet_val, point_map, idealChart_mod]
  exact InfinityBoundaryScheme318.point_origin (a4 n) (a6 n)

theorem idealJet_injective (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Function.Injective (idealJet n I hI) := by
  intro a b hab
  have hv := congrArg Subtype.val hab
  rw [idealJet_val, idealJet_val] at hv
  exact idealChart_injective (coeff n) (a4 n) (a6 n) I hI (ChartInputEquality318.infinity_injective (a4 n) (a6 n) _ _ hv)

theorem exists_idealJet (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (p : pointsFor n T)
    (hp : reduce n I p = 0) : ∃ a : Direction (coeff n) I, idealJet n I hI a = p := by
  let k := specOf n (Ideal.Quotient.mkₐ (coeff n) I)
  let j := WeierstrassGluing318.infinityChart (a4 n) (a6 n)
  have h0 : k ≫ p.val = baseFor n (T ⧸ I) ≫ origin n := by
    have H := congrArg Subtype.val hp
    change (pullPoint n (Ideal.Quotient.mkₐ (coeff n) I) p).val = _ at H
    rw [pullPoint_val] at H
    exact H
  have hr : Set.range p.val ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := quotient_surjective n I hI x
    have hy' : k y = x := hy
    rw [← hy']
    refine ⟨(baseFor n (T ⧸ I) ≫ InfinitySmooth318.infinity (a4 n) (a6 n)) y, ?_⟩
    simpa only [WeierstrassGluing318.infinity, Scheme.Hom.comp_apply] using
      (congrArg (fun f : Spec (CommRingCat.of (T ⧸ I)) ⟶ Curve n => f y) h0).symm
  let P := IsOpenImmersion.lift j p.val hr
  have hP : P ≫ j = p.val := IsOpenImmersion.lift_fac _ _ _
  have hPb : P ≫ Spec.algebraMap (coeff n) (InfinityChart318.Ring (a4 n) (a6 n)) = baseFor n T := by
    change P ≫ InfinitySmooth318.structureMap (a4 n) (a6 n) = _
    rw [← WeierstrassGluing318.infinityChart_structure (a4 n) (a6 n), ← Category.assoc, hP]
    exact p.property
  let f := AffineProductEvaluation318.toAlgHom P hPb
  have hpf : InfinityBoundaryScheme318.point (a4 n) (a6 n) f = p.val := by
    unfold InfinityBoundaryScheme318.point InfinityBoundaryScheme318.chartPoint
    rw [AffineProductEvaluation318.map_toAlgHom P hPb]
    exact hP
  have hf : (Ideal.Quotient.mkₐ (coeff n) I).comp f =
      (Algebra.ofId (coeff n) (T ⧸ I)).comp (InfinityChart318.origin (a4 n) (a6 n)) := by
    apply ChartInputEquality318.infinity_injective (a4 n) (a6 n)
    change InfinityBoundaryScheme318.point (a4 n) (a6 n) ((Ideal.Quotient.mkₐ (coeff n) I).comp f) =
      InfinityBoundaryScheme318.point (a4 n) (a6 n)
        ((Algebra.ofId (coeff n) (T ⧸ I)).comp (InfinityChart318.origin (a4 n) (a6 n)))
    rw [← point_map, hpf, InfinityBoundaryScheme318.point_origin]
    exact h0
  obtain ⟨a, ha⟩ := exists_idealChart (coeff n) (a4 n) (a6 n) I hI f hf
  refine ⟨a, Subtype.ext ?_⟩
  rw [idealJet_val, ← ha, hpf]

/-- Actual [m] on this non-split identity kernel. -/
theorem idealJet_mul (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction (coeff n) I) (m : ℕ) :
    (idealJet n I hI a).val ≫ mulMap n m = (idealJet n I hI (m • a)).val := by
  rw [← mul_value n m (baseFor n T) (idealJet n I hI a)]
  exact congrArg Subtype.val (map_nsmul (idealJet n I hI) m a).symm

/-- Once a genuine preliminary lift is available, correct it by the
actual identity-kernel point. This proves existence and uniqueness on
this test only; it does not assume global lifting for smooth schemes. -/
theorem existsUnique_translated_lift (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥)
    (m : ℕ) (hm : IsUnit (m : (coeff n)))
    (p₀ : pointsFor n (T ⧸ I)) (q p : pointsFor n T)
    (hp : reduce n I p = p₀) (hq : reduce n I q = m • p₀) :
    ∃! t : pointsFor n T, reduce n I t = p₀ ∧ m • t = q := by
  let u : (coeff n)ˣ := hm.unit
  have hu : (u : (coeff n)) = (m : (coeff n)) := hm.unit_spec
  let J := idealJet n I hI
  have hd : reduce n I (q - m • p) = 0 := by
    rw [map_sub, map_nsmul, hp, hq, sub_self]
  obtain ⟨v, hv⟩ := exists_idealJet n I hI (q - m • p) hd
  let w : Direction (coeff n) I := (↑(u⁻¹) : (coeff n)) • v
  have hw : m • w = v := by
    rw [← Nat.cast_smul_eq_nsmul (coeff n), ← hu]
    change (u : (coeff n)) • ((↑(u⁻¹) : (coeff n)) • v) = v
    rw [← mul_smul, Units.mul_inv, one_smul]
  let t := p + J w
  have ht₁ : reduce n I t = p₀ := by
    change reduce n I (p + idealJet n I hI w) = p₀
    rw [map_add, hp, idealJet_reduce, add_zero]
  have ht₂ : m • t = q := by
    change m • (p + J w) = q
    rw [nsmul_add, ← map_nsmul J, hw]
    change m • p + idealJet n I hI v = q
    rw [hv] <;> abel
  refine ⟨t, ⟨ht₁, ht₂⟩, ?_⟩
  intro x hx
  have hx0 : reduce n I (x - t) = 0 := by
    rw [map_sub, hx.1, ht₁, sub_self]
  obtain ⟨v', hv'⟩ := exists_idealJet n I hI (x - t) hx0
  have hz : m • v' = 0 := by
    apply idealJet_injective n I hI
    rw [map_nsmul, hv', map_zero, nsmul_sub, hx.2, ht₂, sub_self]
  have hzu : (u : (coeff n)) • v' = 0 := by
    simpa only [hu, Nat.cast_smul_eq_nsmul (coeff n)] using hz
  have hz' : v' = 0 := by
    have h := congrArg (fun a : Direction (coeff n) I => (↑(u⁻¹) : (coeff n)) • a) hzu
    simpa only [← mul_smul, Units.inv_mul, one_smul, smul_zero] using h
  exact sub_eq_zero.mp (by simpa only [hz', map_zero] using hv'.symm)

end ActualNonSplitIdentityLifts318
