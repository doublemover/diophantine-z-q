module
public import ActualOriginalMinorQuadraticSupremum318
public section
noncomputable section
namespace ActualOriginalPrefixMinorMoment318
open ActualOriginalMinorQuadraticSupremum318 ActualOriginalRectangularMinorMoment318
open ActualOriginalQuadraticEnergyCount318 ActualOriginalMajorArcDomain318
open ActualOriginalFiniteCircleIdentity318 ActualOriginalFiniteBoxProduct318 MeasureTheory

/-- Four actual quadratic moments plus the PRODUCED fifth supremum.
The four first sets may be arbitrary bounded subsets; the fifth must be
an actual interval. This covers every rectangular prefix used by Abel. -/
theorem actual_original_prefix_minor_moment (κ : ℤ) (hκ : κ≠0) (N H : ℕ)
    (hN : 0<N) (B : ℝ) (hB : 0<B) (hs : ((N : ℝ)+1)^3≤B)
    (s0 s1 s2 s3 : Finset ℤ)
    (hs0 : s0⊆Finset.Icc (-(H : ℤ)) H) (hs1 : s1⊆Finset.Icc (-(H : ℤ)) H)
    (hs2 : s2⊆Finset.Icc (-(H : ℤ)) H) (hs3 : s3⊆Finset.Icc (-(H : ℤ)) H)
    (lo hi : ℤ) (hlo : -(H : ℤ)≤lo) (hhi : hi≤H) (δ : ℝ) (hδ : 0<δ) :
    (∫ t in minorDomain N B,
      ‖originalCircleSum κ (originalBox s0 s1 s2 s3 (Finset.Icc lo hi))
        (fun _ => 1) (t : AddCircle (1 : ℝ))‖)≤
      Real.sqrt (minorQuadraticBudget (-κ) H N ⌈B^2/(N : ℝ)⌉₊)*momentBudget H δ := by
  apply actual_original_rectangle_minor_moment κ N H B s0 s1 s2 s3 (Finset.Icc lo hi)
    hs0 hs1 hs2 hs3 δ hδ _ (Real.sqrt_nonneg _)
  intro t ht
  exact actual_minor_quadratic_canonical (-κ) (neg_ne_zero.mpr hκ) H N hN B hB hs
    lo hi hlo hhi t ht

/-- Uniformity in all five interval endpoints is explicit. There is no
supremum inside the integral, and no arbitrary-weight factorization. -/
theorem actual_all_original_prefixes (κ : ℤ) (hκ : κ≠0) (N H : ℕ)
    (hN : 0<N) (B : ℝ) (hB : 0<B) (hs : ((N : ℝ)+1)^3≤B)
    (lo0 hi0 lo1 hi1 lo2 hi2 lo3 hi3 lo4 hi4 : ℤ)
    (hl0 : -(H : ℤ)≤lo0) (hh0 : hi0≤H)
    (hl1 : -(H : ℤ)≤lo1) (hh1 : hi1≤H)
    (hl2 : -(H : ℤ)≤lo2) (hh2 : hi2≤H)
    (hl3 : -(H : ℤ)≤lo3) (hh3 : hi3≤H)
    (hl4 : -(H : ℤ)≤lo4) (hh4 : hi4≤H) (δ : ℝ) (hδ : 0<δ) :
    (∫ t in minorDomain N B,
      ‖originalCircleSum κ (originalBox (Finset.Icc lo0 hi0) (Finset.Icc lo1 hi1)
        (Finset.Icc lo2 hi2) (Finset.Icc lo3 hi3) (Finset.Icc lo4 hi4))
        (fun _ => 1) (t : AddCircle (1 : ℝ))‖)≤
      Real.sqrt (minorQuadraticBudget (-κ) H N ⌈B^2/(N : ℝ)⌉₊)*momentBudget H δ := by
  apply actual_original_prefix_minor_moment κ hκ N H hN B hB hs
    _ _ _ _ _ _ _ _ lo4 hi4 hl4 hh4 δ hδ
  all_goals
    intro x hx
    have hh := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩

end ActualOriginalPrefixMinorMoment318
