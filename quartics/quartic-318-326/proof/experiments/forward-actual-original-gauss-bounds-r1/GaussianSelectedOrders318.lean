module
public import GaussianPrimeSeparation318
public section
noncomputable section
namespace GaussianSelectedOrders318
open GaussianNeighborNorms318 GaussianQuarterModuli318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open ActualSelectedOrderModuli318 SelectedReductionOrder318
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels) (u w : ℤ) (hv : Values C u w)
variable (r : Roots C u w hv) (a b : Fin 3 × Fin 5 → ℤ)

/-- The precise remaining CM identification, at the ORIGINAL chosen roots.
It is not asserted from the Gaussian norm equation or the curve's j-value. -/
@[expose] def CMMatch : Prop := ∀ i : Fin 3 × Fin 5,
  counts C u w hv r false i=GaussianNeighborNorms318.minus (a i) (b i) ∧
  counts C u w hv r true i=GaussianNeighborNorms318.plus (a i) (b i)

theorem quarter_moduli (hcm : CMMatch C u w hv r a b) :
    GaussianRayQuarterPreparation318.quarterMinus C u w hv r=lower a b ∧
    GaussianRayQuarterPreparation318.quarterPlus C u w hv r=upper a b := by
  constructor
  · apply congrArg (Finset.univ.lcm)
    funext i
    rw [(hcm i).1]
  · apply congrArg (Finset.univ.lcm)
    funext i
    rw [(hcm i).2]

/-- All five exact finite CRT conclusions are DERIVED from the displayed
Gaussian outputs, finite growth/separation and actual CM identification.
The analytic existence of those outputs and the CM theorem remain explicit. -/
theorem crt_data (L : ℕ) (hL : 0<L) (h64 : 64∣L)
    (hray : ∀ i, GaussianRayQuadratic318.Ray (row C u w i.1 i.2).natAbs (a i) (b i))
    (hcm : CMMatch C u w hv r a b)
    (hpair : ∀ i j, Nat.gcd (GaussianNeighborNorms318.minus (a i) (b i))
      (GaussianNeighborNorms318.plus (a j) (b j))=4)
    (hav : ∀ i, Avoid L (a i) (b i))
    (hlarge : ∀ k∈coefficients C, L<(value u w k).natAbs)
    (E : ℝ) (herror : ∀ i, 1+2*|(a i:ℝ)|≤E) (hspace : E<(w:ℝ)^2)
    (hrange : ∀ k∈coefficients C, ∀ i : Fin 3 × Fin 5,
      ((row C u w i.1 i.2).natAbs:ℝ)+E<2*((value u w k).natAbs:ℝ)) :
    let Mminus := GaussianRayQuarterPreparation318.quarterMinus C u w hv r
    let Mplus := GaussianRayQuarterPreparation318.quarterPlus C u w hv r
    0<Mminus ∧ 0<Mplus ∧ Nat.Coprime (product C u w) Mplus ∧
      Nat.Coprime (product C u w) L ∧ Nat.Coprime Mminus Mplus ∧
      Nat.Coprime Mplus L ∧ Nat.gcd Mminus L=16 := by
  dsimp only
  obtain ⟨he,hf⟩ := quarter_moduli C u w hv r a b hcm
  rw [he,hf]
  have ha : ∀ i, a i%16=9 := fun i => (hray i).2.1
  have hb : ∀ i, b i%16=0 := fun i => (hray i).2.2
  obtain ⟨hm,hp⟩ := positive a b ha hb
  obtain ⟨hg,hpc⟩ := continuity_gcd a b L h64 ha hb hav
  exact ⟨hm,hp,GaussianPrimeSeparation318.product_coprime_upper C u w hv a b hray E herror hspace hrange,
    GaussianPrimeSeparation318.product_coprime_continuity C u w hv L hL hlarge,
    pair_coprime a b ha hb hpair,hpc,hg⟩

end GaussianSelectedOrders318
