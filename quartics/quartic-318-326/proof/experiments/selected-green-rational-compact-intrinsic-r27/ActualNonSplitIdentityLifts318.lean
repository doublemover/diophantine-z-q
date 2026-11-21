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
    (f : V ⟶ U) (h : f ≫ b = c) : Points n b →+ Points n c where
  toFun p := ⟨f ≫ p.val, by rw [Category.assoc,p.property,h]⟩
  map_zero' := by
    subst c
    exact (precomp n b f).map_zero
  map_add' p q := by
    subst c
    exact (precomp n b f).map_add p q

/-- Actual functorial precomposition over the same literal base. -/
def pullPoint (n : ℕ) {T D : Type} [CommRing T] [CommRing D]
    [Algebra (OpenJModel318.Base n) T] [Algebra (OpenJModel318.Base n) D]
    (f : T →ₐ[coeff n] D) : pointsFor n T →+ pointsFor n D :=
  pullOver n (baseFor n T) (baseFor n D) (specOf n f) (spec_over n f)

private theorem pullPoint_val_internal (n : ℕ) {T D : Type} [CommRing T] [CommRing D]
    [Algebra (OpenJModel318.Base n) T] [Algebra (OpenJModel318.Base n) D]
    (f : T →ₐ[coeff n] D) (p : pointsFor n T) :
    (pullPoint n f p).val = specOf n f ≫ p.val := rfl

@[simp] theorem pullPoint_val (n : ℕ) {T D : Type} [CommRing T] [CommRing D]
    [Algebra (OpenJModel318.Base n) T] [Algebra (OpenJModel318.Base n) D]
    (f : T →ₐ[coeff n] D) (p : pointsFor n T) :
    (pullPoint n f p).val = specOf n f ≫ p.val := by
  exact pullPoint_val_internal n f p

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

private theorem idealJet_outer_val (n : ℕ) {T : Type} [CommRing T]
    [Algebra (OpenJModel318.Base n) T] (I : Ideal T) (hI : I ^ 2 = ⊥)
    (a : Direction (coeff n) I) :
    (idealJet n I hI a).val =
      specOf n (specimen (coeff n) I hI) ≫ (literalJet n (V := Direction (coeff n) I) a).val :=
  pullPoint_val n (specimen (coeff n) I hI) (literalJet n (V := Direction (coeff n) I) a)

private theorem literalChart_val (n : ℕ) {T : Type} [CommRing T]
    [Algebra (OpenJModel318.Base n) T] (I : Ideal T) (a : Direction (coeff n) I) :
    (literalJet n (V := Direction (coeff n) I) a).val =
      InfinityBoundaryScheme318.point (a4 n) (a6 n)
        (ActualInfinitySquareZero318.jet (a4 n) (a6 n) a) := rfl

theorem idealJet_val (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction (coeff n) I) :
    (idealJet n I hI a).val =
      InfinityBoundaryScheme318.point (a4 n) (a6 n) (idealChart (coeff n) (a4 n) (a6 n) I hI a) := by
  calc
    _ = specOf n (specimen (coeff n) I hI) ≫ (literalJet n (V := Direction (coeff n) I) a).val :=
      idealJet_outer_val n I hI a
    _ = specOf n (specimen (coeff n) I hI) ≫ InfinityBoundaryScheme318.point (a4 n) (a6 n)
        (ActualInfinitySquareZero318.jet (a4 n) (a6 n) a) :=
      congrArg (fun f : ActualLiteralIdentityJet318.test (coeff n) (Direction (coeff n) I) ⟶ Curve n =>
        specOf n (specimen (coeff n) I hI) ≫ f) (literalChart_val n I a)
    _ = _ :=
      point_map n (ActualInfinitySquareZero318.jet (a4 n) (a6 n) a) (specimen (coeff n) I hI)

theorem idealJet_val_assoc (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction (coeff n) I) {Z : Scheme} (g : Curve n ⟶ Z) :
    (idealJet n I hI a).val ≫ g =
      InfinityBoundaryScheme318.point (a4 n) (a6 n) (idealChart (coeff n) (a4 n) (a6 n) I hI a) ≫ g :=
  congrArg (fun f : Spec (CommRingCat.of T) ⟶ Curve n => f ≫ g) (idealJet_val n I hI a)

private theorem reduce_val (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (p : pointsFor n T) :
    (reduce n I p).val = specOf n (Ideal.Quotient.mkₐ (coeff n) I) ≫ p.val :=
  pullPoint_val n (Ideal.Quotient.mkₐ (coeff n) I) p

private theorem points_zero_val (n : ℕ) (D : Type) [CommRing D] [Algebra (OpenJModel318.Base n) D] :
    (0 : pointsFor n D).val = baseFor n D ≫ origin n := rfl

private theorem reduce_chart_val (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction (coeff n) I) :
    specOf n (Ideal.Quotient.mkₐ (coeff n) I) ≫
      InfinityBoundaryScheme318.point (a4 n) (a6 n) (idealChart (coeff n) (a4 n) (a6 n) I hI a) =
    baseFor n (T ⧸ I) ≫ origin n := by
  rw [point_map,idealChart_mod]
  exact InfinityBoundaryScheme318.point_origin (a4 n) (a6 n)

theorem idealJet_reduce (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction (coeff n) I) :
    reduce n I (idealJet n I hI a) = 0 := by
  apply Subtype.ext
  calc
    _ = specOf n (Ideal.Quotient.mkₐ (coeff n) I) ≫ (idealJet n I hI a).val :=
      reduce_val n I (idealJet n I hI a)
    _ = specOf n (Ideal.Quotient.mkₐ (coeff n) I) ≫
        InfinityBoundaryScheme318.point (a4 n) (a6 n) (idealChart (coeff n) (a4 n) (a6 n) I hI a) :=
      congrArg (fun f : Spec (CommRingCat.of T) ⟶ Curve n =>
        specOf n (Ideal.Quotient.mkₐ (coeff n) I) ≫ f) (idealJet_val n I hI a)
    _ = baseFor n (T ⧸ I) ≫ origin n := reduce_chart_val n I hI a
    _ = _ := (points_zero_val n (T ⧸ I)).symm

theorem idealJet_injective (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) :
    Function.Injective (idealJet n I hI) := by
  intro a b hab
  have hv := congrArg Subtype.val hab
  rw [idealJet_val, idealJet_val] at hv
  exact idealChart_injective (coeff n) (a4 n) (a6 n) I hI (ChartInputEquality318.infinity_injective (a4 n) (a6 n) _ _ hv)

private theorem exists_geometric_idealJet (n : ℕ) {T : Type} [CommRing T]
    [Algebra (OpenJModel318.Base n) T] (I : Ideal T) (hI : I ^ 2 = ⊥)
    (p : Spec (CommRingCat.of T) ⟶ Curve n)
    (hbase : p ≫ projection n = baseFor n T)
    (h0 : specOf n (Ideal.Quotient.mkₐ (coeff n) I) ≫ p = baseFor n (T ⧸ I) ≫ origin n) :
    ∃ a : Direction (coeff n) I,
      InfinityBoundaryScheme318.point (a4 n) (a6 n) (idealChart (coeff n) (a4 n) (a6 n) I hI a) = p := by
  let k := specOf n (Ideal.Quotient.mkₐ (coeff n) I)
  let j := WeierstrassGluing318.infinityChart (a4 n) (a6 n)
  have hr : Set.range p ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := quotient_surjective n I hI x
    have hy' : k y = x := hy
    rw [← hy']
    refine ⟨(baseFor n (T ⧸ I) ≫ InfinitySmooth318.infinity (a4 n) (a6 n)) y, ?_⟩
    simpa only [WeierstrassGluing318.infinity, Scheme.Hom.comp_apply] using
      (congrArg (fun f : Spec (CommRingCat.of (T ⧸ I)) ⟶ Curve n => f y) h0).symm
  let P := IsOpenImmersion.lift j p hr
  have hP : P ≫ j = p := IsOpenImmersion.lift_fac _ _ _
  have hPb : P ≫ Spec.algebraMap (coeff n) (InfinityChart318.Ring (a4 n) (a6 n)) = baseFor n T := by
    change P ≫ InfinitySmooth318.structureMap (a4 n) (a6 n) = _
    rw [← WeierstrassGluing318.infinityChart_structure (a4 n) (a6 n), ← Category.assoc, hP]
    exact hbase
  let f := AffineProductEvaluation318.toAlgHom P hPb
  have hpf : InfinityBoundaryScheme318.point (a4 n) (a6 n) f = p := by
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
  exact ⟨a,(congrArg (InfinityBoundaryScheme318.point (a4 n) (a6 n)) ha).symm.trans hpf⟩

theorem exists_idealJet (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (p : pointsFor n T)
    (hp : reduce n I p = 0) : ∃ a : Direction (coeff n) I, idealJet n I hI a = p := by
  have h0 : specOf n (Ideal.Quotient.mkₐ (coeff n) I) ≫ p.val =
      baseFor n (T ⧸ I) ≫ origin n :=
    (reduce_val n I p).symm.trans
      ((congrArg (fun q : pointsFor n (T ⧸ I) => q.val) hp).trans (points_zero_val n (T ⧸ I)))
  obtain ⟨a,ha⟩ := exists_geometric_idealJet n I hI p.val p.property h0
  exact ⟨a,Subtype.ext ((idealJet_val n I hI a).trans ha)⟩

/-- Actual [m] on this non-split identity kernel. -/
theorem idealJet_mul (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥) (a : Direction (coeff n) I) (m : ℕ) :
    (idealJet n I hI a).val ≫ mulMap n m = (idealJet n I hI (m • a)).val := by
  exact (mul_value n m (baseFor n T) (idealJet n I hI a)).symm.trans
    (congrArg (fun p : pointsFor n T => p.val) (map_nsmul (idealJet n I hI) m a).symm)

private theorem unit_scalar_bijective (R : Type) [CommRing R] {D : Type}
    [AddCommGroup D] [Module R D] (m : ℕ) (hm : IsUnit (m : R)) :
    Function.Bijective (fun a : D => m • a) := by
  let u : Rˣ := hm.unit
  have hu : (u:R) = (m:R) := hm.unit_spec
  have hv (a : D) : m • a = (u:R) • a := by
    rw [hu,Nat.cast_smul_eq_nsmul R]
  constructor
  · intro a b hab
    have h := congrArg (fun x : D => (↑u⁻¹:R) • x) ((hv a).symm.trans (hab.trans (hv b)))
    simpa only [← mul_smul,Units.inv_mul,one_smul] using h
  · intro a
    refine ⟨(↑u⁻¹:R) • a,?_⟩
    change m • ((↑u⁻¹:R) • a) = a
    exact (hv ((↑u⁻¹:R) • a)).trans (by rw [← mul_smul,Units.mul_inv,one_smul])

private theorem lift_by_kernel {A B D : Type} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup D] (r : A →+ B) (j : D →+ A)
    (hzero : ∀ v, r (j v) = 0) (hinj : Function.Injective j)
    (hker : ∀ a, r a = 0 → ∃ v, j v = a)
    (m : ℕ) (hm : Function.Bijective (fun v : D => m • v))
    (p₀ : B) (q p : A) (hp : r p = p₀) (hq : r q = m • p₀) :
    ∃! t : A, r t = p₀ ∧ m • t = q := by
  have hd : r (q - m • p) = 0 := by
    rw [map_sub,map_nsmul,hp,hq,sub_self]
  obtain ⟨v,hv⟩ := hker _ hd
  obtain ⟨w,hw⟩ := hm.2 v
  let t := p+j w
  have ht₁ : r t = p₀ := by
    change r (p+j w) = p₀
    rw [map_add,hp,hzero,add_zero]
  have ht₂ : m • t = q := by
    change m • (p+j w) = q
    have hw' : m • w = v := hw
    calc
      _ = m • p + m • j w := by rw [nsmul_add]
      _ = m • p + j (m • w) := congrArg (fun a : A => m • p + a) (map_nsmul j m w).symm
      _ = m • p + j v := congrArg (fun a : D => m • p + j a) hw'
      _ = m • p + (q - m • p) := congrArg (fun a : A => m • p + a) hv
      _ = q := by abel
  refine ⟨t,⟨ht₁,ht₂⟩,?_⟩
  intro x hx
  have hx₀ : r (x-t) = 0 := by rw [map_sub,hx.1,ht₁,sub_self]
  obtain ⟨v',hv'⟩ := hker _ hx₀
  have hz : m • v' = 0 := by
    apply hinj
    rw [map_nsmul,hv',map_zero,nsmul_sub,hx.2,ht₂,sub_self]
  have hz' : v' = 0 := hm.1 (hz.trans (nsmul_zero m).symm)
  exact sub_eq_zero.mp (by simpa only [hz',map_zero] using hv'.symm)

/-- Once a genuine preliminary lift is available, correct it by the
actual identity-kernel point. This proves existence and uniqueness on
this test only; it does not assume global lifting for smooth schemes. -/
theorem existsUnique_translated_lift (n : ℕ) {T : Type} [CommRing T] [Algebra (OpenJModel318.Base n) T]
    (I : Ideal T) (hI : I ^ 2 = ⊥)
    (m : ℕ) (hm : IsUnit (m : (coeff n)))
    (p₀ : pointsFor n (T ⧸ I)) (q p : pointsFor n T)
    (hp : reduce n I p = p₀) (hq : reduce n I q = m • p₀) :
    ∃! t : pointsFor n T, reduce n I t = p₀ ∧ m • t = q := by
  exact lift_by_kernel (reduce n I) (idealJet n I hI)
    (idealJet_reduce n I hI) (idealJet_injective n I hI) (exists_idealJet n I hI)
    m (unit_scalar_bijective (coeff n) (D := Direction (coeff n) I) m hm) p₀ q p hp hq

end ActualNonSplitIdentityLifts318
