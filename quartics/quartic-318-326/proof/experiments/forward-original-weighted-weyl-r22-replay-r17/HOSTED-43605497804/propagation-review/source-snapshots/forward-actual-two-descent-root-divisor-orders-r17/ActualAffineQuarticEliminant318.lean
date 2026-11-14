module
public import ActualQuadraticQuarticEliminant318
public section
noncomputable section
namespace ActualAffineQuarticEliminant318
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318
open OriginalAffineSieveEliminants318 ActualGaussianChartObstruction318
set_option maxHeartbeats 8500000

@[expose] def r2 (κ : ℤ) (d : Vector ℤ) := κ*d.2.2^2-d.1*d.2.1
@[expose] def r1 (κ : ℤ) (a d : Vector ℤ) := 2*κ*a.2.2*d.2.2-a.1*d.2.1-d.1*a.2.1
@[expose] def r0 (κ t : ℤ) (a : Vector ℤ) := κ*a.2.2^2-a.1*a.2.1+t^2+2*t
@[expose] def k4 (κ : ℤ) (a d : Vector ℤ) := (r2 κ d)^2
@[expose] def k3 (κ : ℤ) (a d : Vector ℤ) := 2*r2 κ d*r1 κ a d
@[expose] def k2 (κ t : ℤ) (a d : Vector ℤ) :=
  (r1 κ a d)^2+2*r2 κ d*r0 κ t a+t^2*(d.1+d.2.1)^2
@[expose] def k1 (κ t : ℤ) (a d : Vector ℤ) :=
  2*r1 κ a d*r0 κ t a+2*t^2*(a.1+a.2.1)*(d.1+d.2.1)
@[expose] def k0 (κ t : ℤ) (a d : Vector ℤ) :=
  (r0 κ t a)^2+t^2*(a.1+a.2.1)^2

/-- All FIVE coefficients of the literal K at the actual affine point,
not coefficients of unshifted D or values sampled on an unrelated line. -/
theorem actual_quartic (κ t : ℤ) (a d : Vector ℤ) (h : ℤ) :
    K κ t (affine a d h)=k4 κ a d*h^4+k3 κ a d*h^3+
      k2 κ t a d*h^2+k1 κ t a d*h+k0 κ t a d := by
  simp [K,affine,r2,r1,r0,k4,k3,k2,k1,k0,zsmul_eq_mul]
  ring

@[expose] def actualEliminant (κ t : ℤ) (a d : Vector ℤ) : ℤ :=
  ActualQuadraticQuarticEliminant318.eliminant
    (fA true κ t d) (fB true κ t a d) (fC true κ t a)
    (k4 κ a d) (k3 κ a d) (k2 κ t a d) (k1 κ t a d) (k0 κ t a d)

/-- Actual second Gaussian source obstruction produces a divisor of the
TRUE quartic eliminant at the SAME remaining coordinates. This includes
all t+2 primes, t=-2, and leading-coefficient primes. -/
theorem actual_obstruction_eliminates (κ t : ℤ) (a d : Vector ℤ) (h : ℤ) (m : ℕ)
    (ho : Obstruction true κ t (affine a d h) m) : (m:ℤ)∣actualEliminant κ t a d := by
  have hF := ho.1
  have hK := ho.2
  change (m:ℤ)∣P' κ t (affine a d h) at hF
  rw [show P' κ t (affine a d h)=fA true κ t d*h^2+fB true κ t a d*h+fC true κ t a
    from actual_affine_polynomial true κ t a d h] at hF
  rw [actual_quartic] at hK
  exact ActualQuadraticQuarticEliminant318.common_divisor _ _ _ _ _ _ _ _ h _ hF hK

/-- The endpoint is applied at the actual original source point, not
merely an abstract polynomial zero. The only coordinate equation says
that the actual affine point is the actual projection of this slice. -/
theorem original_source_eliminates (κ t : ℤ) (a d : Vector ℤ) (h : ℤ)
    (p : ℕ) [Fact p.Prime] (hp2 : p≠2) (ht : ¬(p:ℤ)∣t)
    (v : LiteralQuarticSlice318.Slice κ t true)
    (hv : affine a d h=LiteralQuarticSlice318.project v.1.1)
    (hG : (p:ℤ)∣G v.1.1) (hH : (p:ℤ)∣H v.1.1) : (p:ℤ)∣actualEliminant κ t a d := by
  apply actual_obstruction_eliminates κ t a d h p
  rw [hv]
  exact (original_source_iff p hp2 κ t ht true v).mp ⟨hG,hH⟩

end ActualAffineQuarticEliminant318
