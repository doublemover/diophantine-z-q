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

variable (n : ℕ)
local notation "R₀" => OpenJModel318.Base n
local notation "A₀" => OpenJAffineScheme318.A n
local notation "B₀" => OpenJAffineScheme318.B n

abbrev baseFor (T : Type) [CommRing T] [Algebra R₀ T] := Spec.algebraMap R₀ T
abbrev pointsFor (T : Type) [CommRing T] [Algebra R₀ T] := Points n (baseFor n T)

variable {T D : Type} [CommRing T] [CommRing D] [Algebra R₀ T] [Algebra R₀ D]

abbrev specOf (f : T →ₐ[R₀] D) := Spec.map (CommRingCat.ofHom f.toRingHom)

private theorem spec_over (f : T →ₐ[R₀] D) : specOf n f ≫ baseFor n T = baseFor n D := by
  change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R₀ T)) =
    Spec.map (CommRingCat.ofHom (algebraMap R₀ D))
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext f.comp_algebraMap

private def pullOver {U V : Scheme} (b : U ⟶ Base n) (c : V ⟶ Base n)
    (f : V ⟶ U) (h : f ≫ b = c) : Points n b →+ Points n c := by
  subst c
  exact precomp n b f

private theorem pullOver_val {U V : Scheme} (b : U ⟶ Base n) (c : V ⟶ Base n)
    (f : V ⟶ U) (h : f ≫ b = c) (p : Points n b) :
    (pullOver n b c f h p).val = f ≫ p.val := by
  subst c
  exact precomp_val n b f p

/-- Actual functorial precomposition over the same literal base. -/
def pullPoint (f : T →ₐ[R₀] D) : pointsFor n T →+ pointsFor n D :=
  pullOver n (baseFor n T) (baseFor n D) (specOf n f) (spec_over n f)

@[simp] theorem pullPoint_val (f : T →ₐ[R₀] D) (p : pointsFor n T) :
    (pullPoint n f p).val = specOf n f ≫ p.val := pullOver_val n _ _ _ _ p

abbrev reduce (I : Ideal T) : pointsFor n T →+ pointsFor n (T ⧸ I) :=
  pullPoint n (Ideal.Quotient.mkₐ R₀ I)

private theorem point_map (f : InfinityChart318.Ring A₀ B₀ →ₐ[R₀] T) (g : T →ₐ[R₀] D) :
    specOf n g ≫ InfinityBoundaryScheme318.point A₀ B₀ f =
      InfinityBoundaryScheme318.point A₀ B₀ (g.comp f) := by
  unfold specOf InfinityBoundaryScheme318.point InfinityBoundaryScheme318.chartPoint
  rw [← Category.assoc, ← Spec.map_comp] <;> rfl

private theorem quotient_surjective (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Function.Surjective (specOf n (Ideal.Quotient.mkₐ R₀ I)) := by
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
  rw [← range_comap_of_surjective f hs] at hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, ?_⟩
  change PrimeSpectrum.comap f y = x
  exact hy

/-- Actual pointed ideal directions, constructed only by the canonical
split specimen map; the coefficient quotient need not split. -/
@[expose] def idealJet (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Direction R₀ I →+ pointsFor n T :=
  (pullPoint n (specimen R₀ I hI)).comp
    { toFun := literalJet n
      map_zero' := literalJet_zero n
      map_add' := literalJet_add n }

@[reassoc] theorem idealJet_val (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction R₀ I) :
    (idealJet n I hI a).val =
      InfinityBoundaryScheme318.point A₀ B₀ (idealChart R₀ A₀ B₀ I hI a) := by
  change (pullPoint n (specimen R₀ I hI) (literalJet n a)).val = _
  rw [pullPoint_val]
  exact point_map n (ActualInfinitySquareZero318.jet A₀ B₀ a) (specimen R₀ I hI)

theorem idealJet_reduce (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction R₀ I) :
    reduce n I (idealJet n I hI a) = 0 := by
  apply Subtype.ext
  change (pullPoint n (Ideal.Quotient.mkₐ R₀ I) (idealJet n I hI a)).val =
    baseFor n (T ⧸ I) ≫ origin n
  rw [pullPoint_val, idealJet_val, point_map, idealChart_mod]
  exact InfinityBoundaryScheme318.point_origin A₀ B₀

theorem idealJet_injective (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Function.Injective (idealJet n I hI) := by
  intro a b hab
  have hv := congrArg Subtype.val hab
  rw [idealJet_val, idealJet_val] at hv
  exact idealChart_injective R₀ A₀ B₀ I hI (ChartInputEquality318.infinity_injective A₀ B₀ _ _ hv)

theorem exists_idealJet (I : Ideal T) (hI : I ^ 2 = ⊥) (p : pointsFor n T)
    (hp : reduce n I p = 0) : ∃ a : Direction R₀ I, idealJet n I hI a = p := by
  let k := specOf n (Ideal.Quotient.mkₐ R₀ I)
  let j := WeierstrassGluing318.infinityChart A₀ B₀
  have h0 : k ≫ p.val = baseFor n (T ⧸ I) ≫ origin n := by
    have H := congrArg Subtype.val hp
    change (pullPoint n (Ideal.Quotient.mkₐ R₀ I) p).val = _ at H
    rw [pullPoint_val] at H
    exact H
  have hr : Set.range p.val ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := quotient_surjective n I hI x
    have hy' : k y = x := hy
    rw [← hy']
    refine ⟨(baseFor n (T ⧸ I) ≫ InfinitySmooth318.infinity A₀ B₀) y, ?_⟩
    simpa only [WeierstrassGluing318.infinity, Scheme.Hom.comp_apply] using
      (congrArg (fun f : Spec (CommRingCat.of (T ⧸ I)) ⟶ Curve n => f y) h0).symm
  let P := IsOpenImmersion.lift j p.val hr
  have hP : P ≫ j = p.val := IsOpenImmersion.lift_fac _ _ _
  have hPb : P ≫ Spec.algebraMap R₀ (InfinityChart318.Ring A₀ B₀) = baseFor n T := by
    change P ≫ InfinitySmooth318.structureMap A₀ B₀ = _
    rw [← WeierstrassGluing318.infinityChart_structure A₀ B₀, ← Category.assoc, hP]
    exact p.property
  let f := AffineProductEvaluation318.toAlgHom P hPb
  have hpf : InfinityBoundaryScheme318.point A₀ B₀ f = p.val := by
    unfold InfinityBoundaryScheme318.point InfinityBoundaryScheme318.chartPoint
    rw [AffineProductEvaluation318.map_toAlgHom P hPb]
    exact hP
  have hf : (Ideal.Quotient.mkₐ R₀ I).comp f =
      (Algebra.ofId R₀ (T ⧸ I)).comp (InfinityChart318.origin A₀ B₀) := by
    apply ChartInputEquality318.infinity_injective A₀ B₀
    change InfinityBoundaryScheme318.point A₀ B₀ ((Ideal.Quotient.mkₐ R₀ I).comp f) =
      InfinityBoundaryScheme318.point A₀ B₀
        ((Algebra.ofId R₀ (T ⧸ I)).comp (InfinityChart318.origin A₀ B₀))
    rw [← point_map, hpf, InfinityBoundaryScheme318.point_origin]
    exact h0
  obtain ⟨a, ha⟩ := exists_idealChart R₀ A₀ B₀ I hI f hf
  refine ⟨a, Subtype.ext ?_⟩
  rw [idealJet_val, ← ha, hpf]

/-- Actual [m] on this non-split identity kernel. -/
theorem idealJet_mul (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction R₀ I) (m : ℕ) :
    (idealJet n I hI a).val ≫ mulMap n m = (idealJet n I hI (m • a)).val := by
  rw [← mul_value n m (baseFor n T) (idealJet n I hI a)]
  exact congrArg Subtype.val (map_nsmul (idealJet n I hI) a m).symm

/-- Once a genuine preliminary lift is available, correct it by the
actual identity-kernel point. This proves existence and uniqueness on
this test only; it does not assume global lifting for smooth schemes. -/
theorem existsUnique_translated_lift (I : Ideal T) (hI : I ^ 2 = ⊥)
    (m : ℕ) (hm : IsUnit (m : R₀))
    (p₀ : pointsFor n (T ⧸ I)) (q p : pointsFor n T)
    (hp : reduce n I p = p₀) (hq : reduce n I q = m • p₀) :
    ∃! t : pointsFor n T, reduce n I t = p₀ ∧ m • t = q := by
  let u : R₀ˣ := hm.unit
  have hu : (u : R₀) = (m : R₀) := hm.unit_spec
  let J := idealJet n I hI
  have hd : reduce n I (q - m • p) = 0 := by
    rw [map_sub, map_nsmul, hp, hq, sub_self]
  obtain ⟨v, hv⟩ := exists_idealJet n I hI (q - m • p) hd
  let w : Direction R₀ I := (↑(u⁻¹) : R₀) • v
  have hw : m • w = v := by
    rw [← Nat.cast_smul_eq_nsmul R₀, ← hu]
    change (u : R₀) • ((↑(u⁻¹) : R₀) • v) = v
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
  have hzu : (u : R₀) • v' = 0 := by
    simpa only [hu, Nat.cast_smul_eq_nsmul R₀] using hz
  have hz' : v' = 0 := by
    have h := congrArg (fun a : Direction R₀ I => (↑(u⁻¹) : R₀) • a) hzu
    simpa only [← mul_smul, Units.inv_mul, one_smul, smul_zero] using h
  exact sub_eq_zero.mp (by simpa only [hz', map_zero] using hv'.symm)

end ActualNonSplitIdentityLifts318
