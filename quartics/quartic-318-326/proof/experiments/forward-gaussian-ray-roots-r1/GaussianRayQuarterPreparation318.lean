module
public import GaussianRayQuadratic318
public section
noncomputable section
namespace GaussianRayQuarterPreparation318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedReductionOrder318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)

/-- Actual Gaussian norm/ray data, not finite-field roots or CM counts. -/
@[expose] def GaussianData : Prop := ∀ i : Fin 3 × Fin 5,
  ∃ a b : ℤ, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs a b

/-- The missing finite root family is now PRODUCED by the actual Gaussian
ray via ordinary quadratic reciprocity, uniformly for both local embeddings. -/
theorem root_data (hdata : GaussianData C u w) : SelectedQuarterOrder318.RootData C u w hv := by
  intro i
  let p := (row C u w i.1 i.2).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hv i.1 i.2⟩
  obtain ⟨a,b,hab⟩ := hdata i
  exact GaussianRayQuadratic318.actual_roots p a b hab

@[expose] def quarterMinus (r : Roots C u w hv) : ℕ :=
  Finset.univ.lcm (fun i => counts C u w hv r false i/4)
@[expose] def quarterPlus (r : Roots C u w hv) : ℕ :=
  Finset.univ.lcm (fun i => counts C u w hv r true i/4)

theorem moduli_compare (r : Roots C u w hv) (hdata : GaussianData C u w)
    (hlarge : ∀ i : Fin 3 × Fin 5, 49<(row C u w i.1 i.2).natAbs) :
    minus C u w hv r∣quarterMinus C u w hv r ∧ plus C u w hv r∣quarterPlus C u w hv r :=
  SelectedQuarterOrder318.actual_moduli_dvd_quarters C u w hv r hlarge (root_data C u w hv hdata)

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- Same original three-pole preparation with actual Gaussian-ray inputs
and quarter-count congruences. Finite roots, p-adic halving and quotient
order comparisons are produced. Existence/compatibility of this same h
and Gaussian prime pattern, plus the CM count formula, remain separate. -/
theorem gaussian_preparation_family (a : ℤ) (hn : ∀ j, labels j≠0)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (h₀ L : ℕ) (N₂ N₃ N₁₇ : ℤ)
    (h₂ : SourceLocalProgression318.Prepared 2 (a:ℚ) labels h₀ L N₂ 3)
    (h₃ : SourceLocalProgression318.Prepared 3 (a:ℚ) labels h₀ L N₃ 1)
    (h₁₇ : SourceLocalProgression318.Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2) :
    ∃ Q : ℕ, 0<Q ∧ ∀ u w : ℤ, ∀ hp : Values C u w,
      (Q:ℤ)∣w → ∀ hray : (∀ k∈coefficients C, (408:ℤ)∣value u w k-1),
      (∀ j : Fin 3, ∀ i : Fin 5, FixedSelectedPrimeBound318.bound C<(row C u w j i).natAbs) →
      GaussianData C u w → ∀ s : Fin 3 × Fin 5 → Bool,
      let r := SelectedRayEmbeddings318.oriented C u w hp (SelectedRayEmbeddings318.roots C u w hp hray) s
      ∀ h : ℕ,
      Nat.ModEq ((MergedContactPrimePattern318.product C u w)^3*quarterMinus C u w hp r) h 0 →
      Nat.ModEq (quarterPlus C u w hp r) h 1 → Nat.ModEq L h h₀ →
      (h:ℤ)≠0 → (h:ℤ)≠1 →
      (∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0) →
      (∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ)
        (parameter C u w) (190+51*j.val) ∧
        ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) (parameter C u w) (190+51*j.val)<17) →
      ThreeSelectedPolePreparation318.Prepared (a:ℚ) labels (h:ℤ) (parameter C u w) := by
  obtain ⟨Q,hQ,hfamily⟩ := SelectedRayEmbeddings318.ray_preparation_family C a hn hbeta hlucas
    h₀ L N₂ N₃ N₁₇ h₂ h₃ h₁₇
  refine ⟨Q,hQ,?_⟩
  intro u w hp hw hray hlarge hdata s h hprimary hopposite hcontinuity hzero hone hg hb
  let r := SelectedRayEmbeddings318.oriented C u w hp (SelectedRayEmbeddings318.roots C u w hp hray) s
  have h49 : ∀ i : Fin 3 × Fin 5, 49<(row C u w i.1 i.2).natAbs := by
    intro i
    have he := hlarge i.1 i.2
    have hbound : 76176≤FixedSelectedPrimeBound318.bound C := by
      unfold FixedSelectedPrimeBound318.bound
      omega
    omega
  have hcomp := moduli_compare C u w hp r hdata h49
  exact hfamily u w hp hw hray hlarge s h
    (hprimary.of_dvd (mul_dvd_mul_left _ hcomp.1)) (hopposite.of_dvd hcomp.2)
    hcontinuity hzero hone hg hb

end GaussianRayQuarterPreparation318