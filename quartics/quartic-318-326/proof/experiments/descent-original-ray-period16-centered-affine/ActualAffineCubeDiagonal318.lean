module
public import ActualCenteredCellCancellation318
public import ActualWrappedAffineCube318
import all ActualWrappedAffineCube318
import all ActualRayPeriod16Interface318
import all OriginalInteriorTelescoping318
public section
noncomputable section
namespace ActualAffineCubeDiagonal318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualWrappedAffineCube318
open ActualRayPeriod16Interface318 ActualSquarefreeWheelConductor16318
open ActualCenteredCellCancellation318

@[expose] def normalizer (r : Row) (a J : ℕ) : ℝ := (r.n:ℝ)*(J:ℝ)^(2*a)
@[expose] def multiplicity (a : ℕ) : ℝ := (2*a+1:ℝ)^(2^a) * (2:ℝ)^(2^a)

/-- The genuine uncentered prime factor, on the original wrapped
cyclic representative. The exact old lower cutoff is retained. -/
@[expose] def primeAt (r : Row) (i : ℕ) (z : ℤ) : ℝ :=
  if (r.cut:ℤ)≤rep r.n z then r.phiRatio*logPrimeRay r.ray (raw r i z) else 0

theorem centered_eq (r : Row) (i : ℕ) (z : ℤ) :
    centeredAt r i z=primeAt r i z-r.mu (raw r i z) := rfl

/-- Affine correlation input, not a centered cube estimate. T is the
set of omitted prime vertices. The means are evaluated at an actual
point of the SAME cell and multiply the FT prime-subset sum. Every
subset has the same comparison main (cell.card times all means).
No division by a possibly zero conditional mean is permitted. -/
def HybridBudget {r : Row} {i a q J : ℕ} (hn : 0<r.n) (hqJ : q*J≤r.n)
    (e : ℝ) : Prop :=
  ∀ (w : Wrap a) (z₀ : Z r.n a J), z₀∈cell (i:=i) hn hqJ w →
    ∀ T ∈ (Finset.univ : Finset (V a)).powerset,
    let μ := fun ω => r.mu (raw r i (input q z₀ ω))
    |hybrid (cell (i:=i) hn hqJ w) (fun z ω => primeAt r i (input q z ω)) μ T -
        ((cell (i:=i) hn hqJ w : Finset (Z r.n a J)).card:ℝ) * (∏ ω : V a, μ ω)|
      ≤ normalizer r a J * e

theorem actual_cube_of_affine_hybrids {r : Row} {i a q J V₀ F : ℕ}
    (hn : 0<r.n) (hJ : 0<J) (hqJ : q*J≤r.n)
    (hW : r.W=2*V₀) (hV : V₀.Coprime 2)
    (h32 : 32∣F) (hF : F∣r.W*16) (hr : RayDyadic r.ray)
    (μ : ℤ→ℝ) (hμ : DyadicSupport μ) (hPeriodic : ∀ p,r.mu p=μ (p%(F:ℤ)))
    (e : ℝ) (he : 0≤e) (affine : HybridBudget (i:=i) (a:=a) hn hqJ e) :
    |linearCube r i a q J|≤multiplicity a * e := by
  let G : Z r.n a J → ℝ := fun z => ∏ ω : V a, centeredAt r i (input q z ω)
  let A : Finset (Z r.n a J) := active (a:=a) (q:=q) (J:=J) r i
  let residual (w : Wrap a) : ℝ := ∑ z ∈ cell (i:=i) hn hqJ w, G z
  have hzero (z : Z r.n a J) (hz : z∉A) : G z=0 := by
    have hbad : ∃ ω : V a, (raw r i (input q z ω))%32≠17 := by
      by_contra h
      apply hz
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ z,fun ω => ?_⟩
      by_contra hh
      exact h ⟨ω,hh⟩
    obtain ⟨ω,hh⟩ := hbad
    exact Finset.prod_eq_zero (Finset.mem_univ ω)
      (actual_centeredAt_zero_off_dyadic r F h32 hr μ hμ hPeriodic i (input q z ω) hh)
  have hreindex : (∑ z : Z r.n a J, G z) = ∑ w : Wrap a, residual w := by
    calc
      _ = ∑ z ∈ A, G z := by
        symm
        apply Finset.sum_subset (Finset.subset_univ A)
        intro z _ hz
        exact hzero z hz
      _ = _ := (Finset.sum_fiberwise A (code hn hqJ) G).symm
  have hs (w : Wrap a) : |residual w|≤ (2:ℝ)^(2^a) * (normalizer r a J * e) := by
    let D : Finset (Z r.n a J) := cell (i:=i) hn hqJ w
    by_cases hw : D.Nonempty
    · obtain ⟨z₀,hz₀⟩ := hw
      let m : V a → ℝ := fun ω => r.mu (raw r i (input q z₀ ω))
      have hfiber : residual w = ∑ z ∈ D, ∏ ω : V a,
          (primeAt r i (input q z ω)-m ω) := by
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.prod_congr rfl
        intro ω _
        rw [centered_eq]
        congr 1
        exact cell_same_mean hW hV hF μ hPeriodic hz hz₀ ω
      rw [hfiber]
      have hb := centered_error D (fun z ω => primeAt r i (input q z ω)) m
        (normalizer r a J * e) (affine w z₀ hz₀)
      simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using hb
    · have hD : D=∅ := Finset.not_nonempty_iff_eq_empty.mp hw
      change |∑ z ∈ D, G z|≤_
      rw [hD,Finset.sum_empty,abs_zero]
      have hn' : (0:ℝ)≤normalizer r a J := by unfold normalizer; positivity
      positivity
  have hA : |∑ z : Z r.n a J, G z|≤
      normalizer r a J * (multiplicity a * e) := by
    rw [hreindex]
    calc
      _ ≤ ∑ w : Wrap a, |residual w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _w : Wrap a, (2:ℝ)^(2^a) * (normalizer r a J * e) :=
        Finset.sum_le_sum fun w _ => hs w
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,wrap_card,
          Nat.cast_pow,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,multiplicity]
        ring
  have hp : 0<normalizer r a J := by unfold normalizer; positivity
  change |(∑ z : Z r.n a J, G z)/normalizer r a J|≤_
  rw [abs_div,abs_of_pos hp,div_le_iff₀ hp]
  exact hA.trans_eq (mul_comm _ _)

theorem row_identity {H : Family} {y N : ℕ} {r : Row} (hr : r∈H.rows y N) :
    r.W=wheel y ∧ r.ray=H.ray ∧ ∀ p,r.mu p=H.fiber (p%(H.conductor:ℤ)) := by
  obtain ⟨b,c,_,_,_,_,rfl,_⟩ := hr
  exact ⟨rfl,rfl,fun _ => rfl⟩

/-- A single already-chosen common slow schedule. At each cutoff
the affine errors must be small at the actual n,J normalizer,
uniform in the specified q and J, not for only one convenient box.
This theorem contains no nonlinear estimate and does not choose a
new schedule. -/
def AffineOnDiagonal (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (E : ℕ→ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N≥N₀,∀ r∈H.rows (Y N) N,
    ∀ i<r.k, ∀ q : ℕ,1≤q → q≤qMax (Y N) → ∀ J : ℕ,
      jMin (Y N) N≤J → J≤jMax (Y N) N →
        ∃ (hn : 0<r.n) (_hJ : 0<J) (hqJ : q*J≤r.n),
          HybridBudget (i:=i) (a:=a) hn hqJ (E N)

theorem linear_of_affine_on_diagonal (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (E : ℕ→ℝ) (delta : ℝ)
    (R : ℕ) (hF : H.conductor=32*R) (hr : RayDyadic H.ray) (hμ : DyadicSupport H.fiber)
    (support : ∃ N₀ : ℕ,∀ N≥N₀, 2≤Y N ∧ R∣oddWheel (Y N))
    (affine : AffineOnDiagonal H Y a qMax jMin jMax E)
    (small : ∃ N₀ : ℕ,∀ N≥N₀,0≤E N ∧ multiplicity a*E N≤delta^(2^a)) :
    LinearOnDiagonal H Y a qMax jMin jMax delta := by
  obtain ⟨Ns,hs⟩ := support
  obtain ⟨Na,ha⟩ := affine
  obtain ⟨Ne,he⟩ := small
  refine ⟨max Ns (max Na Ne),?_⟩
  intro N hN r hrow i hi q hq hqmax J hJmin hJmax
  have hNs := (le_max_left Ns (max Na Ne)).trans hN
  have hNae := (le_max_right Ns (max Na Ne)).trans hN
  have hNa := (le_max_left Na Ne).trans hNae
  have hNe := (le_max_right Na Ne).trans hNae
  obtain ⟨hy,hR⟩ := hs N hNs
  obtain ⟨hn,hJ,hqJ,budget⟩ := ha N hNa r hrow i hi q hq hqmax J hJmin hJmax
  obtain ⟨hW,hray,hmean⟩ := row_identity hrow
  have hW' : r.W=2*oddWheel (Y N) := hW.trans (wheel_split hy)
  have hdiv : H.conductor∣r.W*16 := by
    obtain ⟨d,hh⟩ := hR
    refine ⟨d,?_⟩
    rw [hF,hW',hh]
    ring
  have h32 : 32∣H.conductor := ⟨R,hF⟩
  have hr' : RayDyadic r.ray := hray.symm ▸ hr
  exact (actual_cube_of_affine_hybrids hn hJ hqJ hW'
    (oddWheel_coprime (Y N)) h32 hdiv hr' H.fiber hμ hmean
    (E N) (he N hNe).1 budget).trans (he N hNe).2

/-- The fixed-y FT comparison can be used at any fixed error tolerance
η. T(y) absorbs the fixed-field o_y(1), lattice, powers and cutoff
strip errors. It is NOT requested uniformly in y or in the field. -/
def FixedCutoffRate (H : Family) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (T : ℕ→ℕ) (y₀ : ℕ) (C η : ℝ) : Prop :=
  ∀ y≥y₀, ∀ N≥T y, ∀ r∈H.rows y N,
    ∀ i<r.k, ∀ q : ℕ,1≤q → q≤qMax y → ∀ J : ℕ,
      jMin y N≤J → J≤jMax y N →
        ∃ (hn : 0<r.n) (_hJ : 0<J) (hqJ : q*J≤r.n),
          HybridBudget (i:=i) (a:=a) hn hqJ (C/Real.log (y:ℝ)+η)

/-- Concrete fixed-y rate → actual LinearOnDiagonal checkpoint.
The already requested common diagonal must be slow for this ONE
preselected threshold T. There is no assertion that an arbitrary
or previously chosen schedule works, or that the nonlinear donor
holds at fixed y. -/
theorem linear_of_fixed_rate (H : Family) (Y : ℕ→ℕ) (a : ℕ)
    (qMax : ℕ→ℕ) (jMin jMax : ℕ→ℕ→ℕ) (T : ℕ→ℕ) (y₀ R : ℕ)
    (C η λ delta : ℝ) (hC : 0≤C) (hη : 0≤η)
    (margin : multiplicity a*(λ+η)≤delta^(2^a))
    (hF : H.conductor=32*R) (hr : RayDyadic H.ray) (hμ : DyadicSupport H.fiber)
    (support : ∃ N₀ : ℕ,∀ N≥N₀, 2≤Y N ∧ R∣oddWheel (Y N))
    (rate : FixedCutoffRate H a qMax jMin jMax T y₀ C η)
    (slow : ∃ N₀ : ℕ,∀ N≥N₀, y₀≤Y N ∧ T (Y N)≤N ∧
      0<Real.log (Y N:ℝ) ∧ C≤λ*Real.log (Y N:ℝ)) :
    LinearOnDiagonal H Y a qMax jMin jMax delta := by
  obtain ⟨N₀,h₀⟩ := slow
  let E := fun N => C/Real.log (Y N:ℝ)+η
  apply linear_of_affine_on_diagonal H Y a qMax jMin jMax E delta R hF hr hμ support
  · refine ⟨N₀,?_⟩
    intro N hN
    exact rate (Y N) (h₀ N hN).1 N (h₀ N hN).2.1
  · refine ⟨N₀,?_⟩
    intro N hN
    obtain ⟨_,_,hl,hλ⟩ := h₀ N hN
    have hm : 0≤multiplicity a := by unfold multiplicity; positivity
    refine ⟨add_nonneg (div_nonneg hC hl.le) hη,?_⟩
    exact (mul_le_mul_of_nonneg_left (add_le_add_right ((div_le_iff₀ hl).2 hλ) η) hm).trans margin

end ActualAffineCubeDiagonal318
