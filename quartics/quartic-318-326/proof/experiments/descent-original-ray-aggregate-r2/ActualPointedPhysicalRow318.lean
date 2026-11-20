module
public import ActualRayConditionalLower318
public import ActualRayPointedAnchor318
public section
noncomputable section
namespace ActualPointedPhysicalRow318

open scoped BigOperators
open OriginalInteriorTelescoping318 ActualRayPointedAnchor318
open ActualRayLiteralInteriorWeight318 ActualRayInteriorMassRectangles318
open ActualRayConditionalLower318 ActualRayConductorRows318 ActualRayPeriodicRectangle318

/-- Use the old physical cleaning: on the dummy support the exact
signed pointed difference survives unchanged as raw product-log
mass minus the actual finite periodic mean table. -/
theorem actual_signed_row_identity (r : Row) (hn : 0<r.n) (F b c : ℕ) (μ : ℤ→ℝ)
    (hb : r.b=(b:ℤ)) (hc : r.c=(c:ℤ)) (hμ : ∀ a,r.mu a=μ (a%(F:ℤ)))
    (hwrap : ∀ z,dummy r z=1→∀ i<r.k,noWrap r i z)
    (hcut : ∀ z,dummy r z=1→∀ i<r.k,
      (r.cut:ℤ)≤baseIndex r z+shift r i (stepIndex r z)) :
    r.phiRatio^r.k*rowRaw r-
      rectangle (fold (table F r.k (d r) μ) F r.W b c) (start r.n) 1 (width r.n) r.M =
      ∑ j∈Finset.range r.k, correlation r hn j (center r j) := by
  have h := row_difference r hn
  rw [prime_mass_exact r hn hwrap hcut,mean_mass_exact r hn F b c μ hb hc hμ hwrap] at h
  simpa only [rowRaw] using h

/-- For this lower-oriented endpoint the external nonlinear input need
only bound the signed sum of the actual anchored tests FROM BELOW. The
same finite-CRT strip error is kept; no reverse inequality is required. -/
theorem actual_signed_row_lower (r : Row) (hn : 0<r.n) (F b c : ℕ)
    (hW : 0<r.W) (hF : 0<F) (μ : ℤ→ℝ) (hμ : ∀ a,0≤μ a ∧ μ a≤1)
    (hb : r.b=(b:ℤ)) (hc : r.c=(c:ℤ)) (hMean : ∀ a,r.mu a=μ (a%(F:ℤ)))
    (hwrap : ∀ z,dummy r z=1→∀ i<r.k,noWrap r i z)
    (hcut : ∀ z,dummy r z=1→∀ i<r.k,
      (r.cut:ℤ)≤baseIndex r z+shift r i (stepIndex r z))
    (allowance : ℝ) (h : -allowance≤∑ j∈Finset.range r.k,correlation r hn j (center r j)) :
    (width r.n:ℝ)*(r.M:ℝ)*rowMean r F b c μ-allowance-
      ((r.W.lcm F/r.W:ℕ):ℝ)*((width r.n:ℝ)+(r.M:ℝ)) ≤ r.phiRatio^r.k*rowRaw r := by
  rw [←actual_signed_row_identity r hn F b c μ hb hc hMean hwrap hcut] at h
  have hp := fixed_conductor_row_error (table F r.k (d r) μ) F r.W b c hW hF
    (start r.n) 1 (width r.n) r.M 1 (table_bounds F r.k (d r) μ hμ)
  have hneg := (abs_le.mp hp).1
  simp only [rowMean,mul_one] at hneg ⊢
  linarith only [h,hneg]

end ActualPointedPhysicalRow318
