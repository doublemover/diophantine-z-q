module
public import GaussianSelectedOrders318
public section
noncomputable section
namespace GaussianIndexPreparation318
open Filter CircuitReplay
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open GaussianRayQuarterPreparation318 GaussianQuarterModuli318
open ActualCyclicClosure318 GeneratorScalarProgression318
open scoped Topology
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)
local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A pre-prime real threshold and divisibility modulus, followed by actual
Gaussian prime/count output, produce the SAME arbitrarily large h with
all three CRT residues, original real guards, fixed roots and prepared
stored poles. No final-index or real-region witness is supplied by the caller.
The precise CM and analytic prime-pattern outputs remain explicit. -/
theorem prepared_family (S : ℚ) (a : ℤ) (hn : ∀ j, labels j≠0)
    (hbeta : labels 0=3723*(2*a+1)^2)
    (hlucas : (labels 2)^2-labels 1*(labels 1-2)*labels 2*labels 3+
      (labels 1-2)^2*(labels 3)^2=1)
    (h₀ L : ℕ) (hL : 0<L) (h64L : 64∣L) (h64h : 64∣h₀)
    (N₂ N₃ N₁₇ : ℤ)
    (h₂ : SourceLocalProgression318.Prepared 2 (a:ℚ) labels h₀ L N₂ 3)
    (h₃ : SourceLocalProgression318.Prepared 3 (a:ℚ) labels h₀ L N₃ 1)
    (h₁₇ : SourceLocalProgression318.Prepared 17 (a:ℚ) labels h₀ L N₁₇ 2) :
    ∃ T : ℚ, ∃ Q : ℕ, 0<Q ∧ ∀ u w : ℤ, ∀ hp : Values C u w,
      (Q:ℤ)∣w → ∀ hray : (∀ k∈coefficients C, (408:ℤ)∣value u w k-1),
      (∀ j : Fin 3, ∀ i : Fin 5, FixedSelectedPrimeBound318.bound C<(row C u w j i).natAbs) →
      ∀ A B : Fin 3 × Fin 5 → ℤ,
      (∀ i, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (A i) (B i)) →
      ∀ s : Fin 3 × Fin 5 → Bool,
      let r := SelectedRayEmbeddings318.oriented C u w hp (SelectedRayEmbeddings318.roots C u w hp hray) s
      GaussianSelectedOrders318.CMMatch C u w hp r A B →
      (∀ i j, Nat.gcd (GaussianNeighborNorms318.minus (A i) (B i))
        (GaussianNeighborNorms318.plus (A j) (B j))=4) →
      (∀ i, Avoid L (A i) (B i)) →
      (∀ k∈coefficients C, L<(value u w k).natAbs) →
      ∀ E : ℝ, (∀ i, 1+2*|(A i:ℝ)|≤E) → E<(w:ℝ)^2 →
      (∀ k∈coefficients C, ∀ i : Fin 3 × Fin 5,
        ((row C u w i.1 i.2).natAbs:ℝ)+E<2*((value u w k).natAbs:ℝ)) →
      T≤parameter C u w → ∀ B₀ : ℕ,
      ∃ h : ℕ, B₀<h ∧ 1<h ∧
        Nat.ModEq ((product C u w)^3*quarterMinus C u w hp r) h 0 ∧
        Nat.ModEq (quarterPlus C u w hp r) h 1 ∧ Nat.ModEq L h h₀ ∧
        (1/100:ℝ)< |(normCoefficient (CoherentMultipleCharts318.chartU (h:ℤ)):ℝ)| ∧
        (∀ j : Fin 4, margin labels j<
          |(RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P):ℝ)|) ∧
        ThreeSelectedPolePreparation318.Prepared (a:ℚ) labels (h:ℤ) (parameter C u w) ∧
        let pre := ThreeDetectorUniformFamily318.witness (a:ℚ) labels (h:ℤ) (parameter C u w)
        pre 0=(a:ℚ) ∧ Constraints (ThreeDetectorPrePole318.rows S) pre ∧
        (∀ j : Fin 3, 0<pre (190+51*j.val) ∧ pre (190+51*j.val)<17) ∧
        (∀ j : Fin 4, RealGuardWitness318.root (CoherentMultiplePrefix318.u labels (h:ℤ))
          (CoherentMultiplePrefix318.v labels (h:ℤ)) j=CoherentMultipleCharts318.fixedRoot (labels j)) ∧
        (∀ P₀ : NormalizedPolePoints318.PointPair (pre 190),
         ∀ P₁ : NormalizedPolePoints318.PointPair (pre 241),
         ∀ P₂ : NormalizedPolePoints318.PointPair (pre 292),
         ∃ out : Assignment, out 0=(a:ℚ) ∧
           (∀ j : Fin 3, out (190+51*j.val)=pre (190+51*j.val)) ∧
           Constraints ((Raw318FinalReplay.stage0 S).take 263) out) := by
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp
    (ThreeDetectorCRTWitness318.prepared_family S (a:ℚ) labels hn)
  obtain ⟨Q,hQ,hprepare⟩ := gaussian_preparation_family C a hn hbeta hlucas
    h₀ L N₂ N₃ N₁₇ h₂ h₃ h₁₇
  refine ⟨T,Q,hQ,?_⟩
  intro u w hp hw hray hlarge A B hGaussian s
  dsimp only
  intro hcm hpair hav hcut E herror hspace hrange hparam B₀
  let r := SelectedRayEmbeddings318.oriented C u w hp (SelectedRayEmbeddings318.roots C u w hp hray) s
  obtain ⟨hm,hp',hPm,hPL,hmp,hpL,hmL⟩ := GaussianSelectedOrders318.crt_data C u w hp r A B
    L hL h64L hGaussian hcm hpair hav hcut E herror hspace hrange
  obtain ⟨h,hbig,hprimary,hopposite,hcontinuity,hscalar,hguards,hin,hrows,hbs,hsigns,hfinish⟩ :=
    hT (parameter C u w) hparam (product C u w) (quarterMinus C u w hp r)
      (quarterPlus C u w hp r) L h₀ 3 (B₀+1) (product_pos C u w hp) hm hp' hL
      hPm hPL hmp hpL hmL h64L h64h
  have h0 : (h:ℤ)≠0 := by omega
  have h1 : (h:ℤ)≠1 := by omega
  have hg : ∀ j, RealGuardTrace318.guardValue (labels j) ((h:ℤ) • LocalGenerator318.P)≠0 := by
    intro j hz
    have he := hguards j
    have hmpos := margin_positive labels hn j
    rw [hz,Rat.cast_zero,abs_zero] at he
    linarith
  have hdata : GaussianData C u w := fun i => ⟨A i,B i,hGaussian i⟩
  have hprep := hprepare u w hp hw hray hlarge hdata s h hprimary hopposite hcontinuity h0 h1 hg hbs
  exact ⟨h,by omega,by omega,hprimary,hopposite,hcontinuity,hscalar,hguards,hprep,
    hin,hrows,hbs,hsigns,hfinish⟩

end GaussianIndexPreparation318
