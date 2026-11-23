module
public import SelectedSameABicanonicalYuanFrame318
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.Tactic

/-! Global generated Hodge ideal → actual raw-KS height endpoint. All finite
place norms are computed from one finite nonzero generating set. Neither a list
of local bases nor a family of finite inequalities is an input. -/
public section
noncomputable section

namespace OriginalGlobalHodgeIdealHeight318

open scoped nonZeroDivisors
open NumberField SectionHeight318 SelectedSameADirectBicanonicalHeight318

variable {F : Type*} [Field F] [NumberField F]

/-- The coefficient module of an integral line, in the named rational frame η.
No simultaneous global generator is needed, even when the ideal is nonprincipal. -/
@[expose] def coeffModule (G : Finset F) : Submodule (𝓞 F) F :=
  Submodule.span (𝓞 F) (G : Set F)

@[expose] def radius (G : Finset F) (hG : G.Nonempty) (v : FinitePlace F) : ℝ :=
  G.sup' hG (fun a => v a)

theorem radius_pos (G : Finset F) (hG : G.Nonempty) (nz : ∀ g ∈ G, g ≠ 0)
    (v : FinitePlace F) : 0 < radius G hG v := by
  obtain ⟨g, hg⟩ := hG
  exact (v.val.pos (nz g hg)).trans_le (Finset.le_sup' (fun a : F => v a) hg)

theorem radius_support (G : Finset F) (hG : G.Nonempty) (nz : ∀ g ∈ G, g ≠ 0) :
    Function.HasFiniteMulSupport (radius G hG) := by
  classical
  have hfin : (⋃ a ∈ (G : Set F), Function.mulSupport (fun w : FinitePlace F => w a)).Finite :=
    G.finite_toSet.biUnion fun a ha => FinitePlace.hasFiniteMulSupport (nz a ha)
  refine hfin.subset ?_
  intro w hw
  by_contra hn
  have h1 (g : F) (hg : g ∈ G) : w g = 1 := by
    by_contra h
    exact hn (Set.mem_iUnion.mpr ⟨g, Set.mem_iUnion.mpr ⟨hg, h⟩⟩)
  have hw1 : radius G hG w = 1 := by
    apply le_antisymm
    · exact Finset.sup'_le hG _ fun g hg => (h1 g hg).le
    · obtain ⟨g, hg⟩ := hG
      exact (h1 g hg).symm.le.trans (Finset.le_sup' (fun a : F => w a) hg)
  exact hw hw1

/-- The normalized finite-place ball is a module over the original integers. -/
@[expose] def ball (v : FinitePlace F) (r : ℝ) (hr : 0 ≤ r) : Submodule (𝓞 F) F where
  carrier := {x | v x ≤ r}
  zero_mem' := by simpa only [Set.mem_setOf_eq, map_zero] using hr
  add_mem' := fun hx hy => (FinitePlace.add_le v _ _).trans (max_le hx hy)
  smul_mem' a x hx := by
    have ha : v (a : F) ≤ 1 := by
      rw [← FinitePlace.norm_embedding_eq]
      exact FinitePlace.norm_le_one F v.maximalIdeal a
    change v.val ((a : F) * x) ≤ r
    rw [map_mul]
    calc
      v.val (a : F) * v.val x ≤ 1 * v.val x := mul_le_mul_of_nonneg_right ha (v.val.nonneg _)
      _ ≤ r := by simpa only [one_mul] using hx

theorem mem_bound (G : Finset F) (hG : G.Nonempty) (nz : ∀ g ∈ G, g ≠ 0)
    (w : FinitePlace F) {x : F} (hx : x ∈ coeffModule G) :
    w x ≤ radius G hG w := by
  have h : coeffModule G ≤ ball w (radius G hG w) (radius_pos G hG nz w).le :=
    Submodule.span_le.mpr fun g hg => Finset.le_sup' (fun a : F => w a) hg
  exact h hx

/-- Thus the radius depends only on the actual coefficient module. -/
theorem radius_eq_of_span_eq (G J : Finset F) (hG : G.Nonempty) (hJ : J.Nonempty)
    (nG : ∀ g ∈ G, g ≠ 0) (nJ : ∀ j ∈ J, j ≠ 0)
    (hm : coeffModule G = coeffModule J) (w : FinitePlace F) :
    radius G hG w = radius J hJ w := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro g hg
    apply mem_bound J hJ nJ w
    rw [← hm]
    exact Submodule.subset_span hg
  · apply Finset.sup'_le
    intro j hj
    apply mem_bound G hG nG w
    rw [hm]
    exact Submodule.subset_span hj

theorem square_mem_bound (G : Finset F) (hG : G.Nonempty) (nz : ∀ g ∈ G, g ≠ 0)
    (w : FinitePlace F) {z : F} (hz : z ∈ coeffModule G * coeffModule G) :
    w z ≤ radius G hG w ^ 2 := by
  have h : coeffModule G * coeffModule G ≤ ball w (radius G hG w ^ 2) (sq_nonneg _) := by
    apply Submodule.mul_le.mpr
    intro a ha b hb
    change w.val (a * b) ≤ radius G hG w ^ 2
    rw [map_mul, pow_two]
    exact mul_le_mul (mem_bound G hG nz w ha) (mem_bound G hG nz w hb)
      (w.val.nonneg _) (radius_pos G hG nz w).le
  exact h hz

/-- The section of the original line on D(n) lies in its genuine
localized scalar span in F. Clear its denominators rather than assuming that
a global exponent or a finite place lift has been supplied. -/
theorem open_span_clears {S : Type*} [CommRing S] [Algebra (𝓞 F) S]
    [Algebra S F] [IsScalarTower (𝓞 F) S F] (n : 𝓞 F) [IsLocalization.Away n S]
    (P : Submodule (𝓞 F) F) {z : F} (hz : z ∈ Submodule.span S (P : Set F)) :
    ∃ k : ℕ, n ^ k • z ∈ P := by
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb ia ib =>
    obtain ⟨k, hk⟩ := ia
    obtain ⟨l, hl⟩ := ib
    refine ⟨k+l, ?_⟩
    rw [smul_add]
    apply P.add_mem
    · rw [Nat.add_comm, pow_add, mul_smul]
      exact P.smul_mem _ hk
    · rw [pow_add, mul_smul]
      exact P.smul_mem _ hl
  | smul s x hx ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨l, a, ha⟩ := IsLocalization.Away.surj n s
    have hs := congrArg (algebraMap S F) ha
    simp only [map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at hs
    have he : n ^ (k+l) • (s • x) = a • (n ^ k • x) := by
      simp only [Algebra.smul_def, map_pow, pow_add]
      calc
        _ = (algebraMap S F s * (algebraMap (𝓞 F) F n) ^ l) *
            ((algebraMap (𝓞 F) F n)^k * x) := by ring
        _ = _ := by rw [hs]
    exact ⟨k+l, he.symm ▸ P.smul_mem a hk⟩

/-- M²[1/3] ∩ M²[1/11] = M² inside the SAME generic line. -/
theorem complementary {P : Submodule (𝓞 F) F} {z : F}
    (h3 : ∃ k : ℕ, (3 : 𝓞 F)^k • z ∈ P) (h11 : ∃ l : ℕ, (11 : 𝓞 F)^l • z ∈ P) :
    z ∈ P := by
  obtain ⟨k, hk⟩ := h3
  obtain ⟨l, hl⟩ := h11
  have hcop : IsCoprime (3 : 𝓞 F) 11 := ⟨4, -1, by norm_num⟩
  obtain ⟨r, s, h⟩ := hcop.pow (m := k) (n := l)
  have hz : z = r • ((3 : 𝓞 F)^k • z) + s • ((11 : 𝓞 F)^l • z) := by
    rw [← mul_smul, ← mul_smul, ← add_smul, h, one_smul]
  rw [hz]
  exact P.add_mem (P.smul_mem r hk) (P.smul_mem s hl)

/-- Construct the adelic norm of η from its global integral line and its
actual archimedean norm. The finite part is 1/max |g|, not max |g|. -/
@[expose] def hodge (G : Finset F) (hG : G.Nonempty) (nz : ∀ g ∈ G, g ≠ 0)
    (A : InfinitePlace F → ℝ) (hA : ∀ w, 0 < A w) : FrameNorms F where
  arch := A
  arch_pos := hA
  finiteNorm w := (radius G hG w)⁻¹
  finite_pos w := inv_pos.mpr (radius_pos G hG nz w)
  finite_support := (radius_support G hG nz).inv

/-- Ξ=Ψ(η²) has the *raw* Yuan isometry at infinity and the single
factor 210 in the finite coefficient, prior to any point pullback. -/
@[expose] def raw (H : FrameNorms F) : FrameNorms F where
  arch w := H.arch w ^ 2
  finiteNorm w := w.val (210 : F) * H.finiteNorm w ^ 2
  arch_pos w := pow_pos (H.arch_pos w) _
  finite_pos w := mul_pos (w.val.pos (by norm_num)) (pow_pos (H.finite_pos w) _)
  finite_support := (FinitePlace.hasFiniteMulSupport (by norm_num : (210 : F) ≠ 0)).mul
    (H.finite_support.pow 2)

/-- Exact shift to the Hodge integral line on pulling back the primitive KS
inverse. a is already 25725/4 times (32,t); c is Q/Ψ(η²) on the same generic
fibre and the same point, *not* an independently selected local scale. -/
@[expose] def hodgeCoefficient (t : ℚ) (c : F) (i : Fin 2) : F :=
  (210 : F) * c * coefficients (F := F) t i

theorem height_of_complementary_hodge_sections
    (G : Finset F) (hG : G.Nonempty) (nz : ∀ g ∈ G, g ≠ 0)
    (A : InfinitePlace F → ℝ) (hA : ∀ w, 0 < A w)
    (t : ℚ) (c : F) (hc : c ≠ 0)
    (onThree : ∀ i, ∃ k : ℕ, (3 : 𝓞 F)^k • hodgeCoefficient t c i ∈ coeffModule G * coeffModule G)
    (onEleven : ∀ i, ∃ l : ℕ, (11 : 𝓞 F)^l • hodgeCoefficient t c i ∈ coeffModule G * coeffModule G)
    (arch : ∀ w : InfinitePlace F, ∃ U f : ℝ,
      2 * max 32 (w (t : F)) ≤ U ∧ 64 ≤ f ∧ w.val c * (A w)^2 = 4/(U*f)) :
    Height.logHeight₁ (t / 32) < 2 * (hodge G hG nz A hA).normalizedDegree + 11 := by
  let H := hodge G hG nz A hA
  let X := raw H
  let Q := X.rescale c hc
  apply SelectedSameABicanonicalYuanFrame318.height_of_raw_ks_places t Q X H c hc
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  · intro w
    change (w.val (210 : F) * H.finiteNorm w ^ 2) / w.val (210 : F) = H.finiteNorm w ^ 2
    exact mul_div_cancel_left₀ _ (w.val.ne_zero_iff.mpr (by norm_num))
  · exact arch
  · intro w i
    have hi := square_mem_bound G hG nz w (complementary (onThree i) (onEleven i))
    change w.val (hodgeCoefficient t c i) ≤ radius G hG w ^ 2 at hi
    simp only [hodgeCoefficient, map_mul] at hi
    change w.val (coefficients (F := F) t i) * (w.val c *
      (w.val (210 : F) * (radius G hG w)⁻¹ ^ 2)) ≤ 1
    calc
      _ = (w.val (210 : F) * w.val c * w.val (coefficients (F := F) t i)) /
          radius G hG w ^ 2 := by rw [div_eq_mul_inv, inv_pow]; ring
      _ ≤ 1 := (div_le_one₀ (sq_pos_of_pos (radius_pos G hG nz w))).mpr hi

/-- Any honest, nonzero Hodge fractional ideal supplies this presentation
over the integers of the one marked number field. Zero may be erased without
changing its span. -/
theorem nonzero_generators (I : FractionalIdeal (𝓞 F)⁰ F) (hn : I ≠ 0) :
    ∃ G : Finset F, G.Nonempty ∧ (∀ g ∈ G, g ≠ 0) ∧
      coeffModule G = (I : Submodule (𝓞 F) F) := by
  classical
  obtain ⟨S, hS⟩ := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  have he : coeffModule (S.erase 0) = (I : Submodule (𝓞 F) F) := by
    simpa only [coeffModule, Finset.coe_erase, Submodule.span_sdiff_singleton_zero] using hS
  refine ⟨S.erase 0, ?_, fun g hg => (Finset.mem_erase.mp hg).1, he⟩
  by_contra hem
  have hz : S.erase 0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hem
  have hib : (I : Submodule (𝓞 F) F) = ⊥ := by simpa [hz, coeffModule] using he.symm
  exact hn (FractionalIdeal.coeToSubmodule_eq_bot.mp hib)

@[expose] def idealFrame (I : FractionalIdeal (𝓞 F)⁰ F) (hn : I ≠ 0)
    (A : InfinitePlace F → ℝ) (hA : ∀ w, 0 < A w) : FrameNorms F :=
  hodge (nonzero_generators I hn).choose (nonzero_generators I hn).choose_spec.1
    (nonzero_generators I hn).choose_spec.2.1 A hA

/-- Single genuine global integral coefficient ideal; the two open restrictions
are exactly the outputs of the two original-model section pullbacks. There is
no quantification over unknown finite place norms or auxiliary frames. -/
theorem height_of_original_hodge_ideal (I : FractionalIdeal (𝓞 F)⁰ F) (hn : I ≠ 0)
    (A : InfinitePlace F → ℝ) (hA : ∀ w, 0 < A w) (t : ℚ) (c : F) (hc : c ≠ 0)
    (onThree : ∀ i, ∃ k : ℕ, (3 : 𝓞 F)^k • hodgeCoefficient t c i ∈
      (I : Submodule (𝓞 F) F) * (I : Submodule (𝓞 F) F))
    (onEleven : ∀ i, ∃ l : ℕ, (11 : 𝓞 F)^l • hodgeCoefficient t c i ∈
      (I : Submodule (𝓞 F) F) * (I : Submodule (𝓞 F) F))
    (arch : ∀ w : InfinitePlace F, ∃ U f : ℝ,
      2 * max 32 (w (t : F)) ≤ U ∧ 64 ≤ f ∧ w.val c * (A w)^2 = 4/(U*f)) :
    Height.logHeight₁ (t / 32) < 2 * (idealFrame I hn A hA).normalizedDegree + 11 := by
  let G := (nonzero_generators I hn).choose
  have hG := (nonzero_generators I hn).choose_spec
  apply height_of_complementary_hodge_sections G hG.1 hG.2.1 A hA t c hc
  · simpa only [G, hG.2.2] using onThree
  · simpa only [G, hG.2.2] using onEleven
  · exact arch

/-- The actual global height cut accepts the sections over the two
complementary affine bases with their honest coefficient rings. -/
theorem height_of_open_sections {S₃ S₁₁ : Type*} [CommRing S₃] [CommRing S₁₁]
    [Algebra (𝓞 F) S₃] [Algebra S₃ F] [IsScalarTower (𝓞 F) S₃ F]
    [Algebra (𝓞 F) S₁₁] [Algebra S₁₁ F] [IsScalarTower (𝓞 F) S₁₁ F]
    [IsLocalization.Away (3 : 𝓞 F) S₃] [IsLocalization.Away (11 : 𝓞 F) S₁₁]
    (I : FractionalIdeal (𝓞 F)⁰ F) (hn : I ≠ 0)
    (A : InfinitePlace F → ℝ) (hA : ∀ w, 0 < A w) (t : ℚ) (c : F) (hc : c ≠ 0)
    (onThree : ∀ i, hodgeCoefficient t c i ∈ Submodule.span S₃
      (↑((I : Submodule (𝓞 F) F) * (I : Submodule (𝓞 F) F)) : Set F))
    (onEleven : ∀ i, hodgeCoefficient t c i ∈ Submodule.span S₁₁
      (↑((I : Submodule (𝓞 F) F) * (I : Submodule (𝓞 F) F)) : Set F))
    (arch : ∀ w : InfinitePlace F, ∃ U f : ℝ,
      2 * max 32 (w (t : F)) ≤ U ∧ 64 ≤ f ∧ w.val c * (A w)^2 = 4/(U*f)) :
    Height.logHeight₁ (t / 32) < 2 * (idealFrame I hn A hA).normalizedDegree + 11 :=
  height_of_original_hodge_ideal I hn A hA t c hc
    (fun i => open_span_clears (S := S₃) 3 _ (onThree i))
    (fun i => open_span_clears (S := S₁₁) 11 _ (onEleven i)) arch

end OriginalGlobalHodgeIdealHeight318
