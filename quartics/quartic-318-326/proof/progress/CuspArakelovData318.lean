module
public import ActualCuspEstimates318
public import ActualWronskian318
public import MetricCancellation318
public section
noncomputable section
namespace CuspArakelovData318
open NumberField MeasureTheory Metric Function
set_option maxHeartbeats 0
variable (K:Type*) [Field K] [NumberField K]

@[expose] def embeddingAverage (f:(K→+*ℂ)→ℝ) : ℝ :=
  MetricCancellation318.average Finset.univ (Module.finrank ℚ K) f

theorem embedding_average_le (f:(K→+*ℂ)→ℝ) (C:ℝ) (hf:∀sigma,f sigma≤C) :
    embeddingAverage K f≤C := by
  have hd : (0:ℝ)<Module.finrank ℚ K := by exact_mod_cast (Module.finrank_pos (R:=ℚ) (M:=K))
  unfold embeddingAverage MetricCancellation318.average
  apply (div_le_iff₀ hd).mpr
  have hh : (∑sigma:(K→+*ℂ),f sigma)≤∑sigma:(K→+*ℂ),C :=
    Finset.sum_le_sum (fun sigma _=>hf sigma)
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Embeddings.card,mul_comm] using hh

theorem embedding_average_neg (f:(K→+*ℂ)→ℝ) :
    embeddingAverage K (fun sigma=> -f sigma)= -embeddingAverage K f := by
  simp only [embeddingAverage,MetricCancellation318.average,Finset.sum_neg_distrib,neg_div]

/-- Source-coordinate data for every actual complex embedding. The ordinary
energy restriction and modular G identification are explicit producer fields. -/
structure Data (g i N:ℕ) where
  G:ℂ→ℂ
  holomorphicG:∀z,‖z‖≤(1:ℝ)/100 → DifferentiableAt ℂ G z
  boundG:∀z,‖z‖≤(1:ℝ)/100 → ‖G z‖≤128
  zeroG:G 0=1
  width:(K→+*ℂ)→ℕ
  width_pos:∀sigma,1≤width sigma
  width_level:∀sigma,width sigma≤N
  tau:(K→+*ℂ)→UpperHalfPlane
  fundamental:∀sigma,Real.sqrt 3/2≤(tau sigma).im
  selected_value:∀sigma,G (Periodic.qParam 1 (tau sigma))=
    Periodic.qParam 1 (tau sigma)*(1728*((2:ℂ)^128+i))
  f:(K→+*ℂ)→Fin g→ℂ→ℂ
  holomorphic:∀sigma j,DifferentiableOn ℂ (f sigma j)
    (ball (Periodic.qParam (width sigma) (tau sigma)) (CuspRadius318.radius (width sigma)))
  integrable:∀sigma j,IntegrableOn (fun z:ℂ=>‖f sigma j z‖^2)
    (ball (Periodic.qParam (width sigma) (tau sigma)) (CuspRadius318.radius (width sigma)))
  energy:∀sigma j,(∫z in ball (Periodic.qParam (width sigma) (tau sigma))
    (CuspRadius318.radius (width sigma)),‖f sigma j z‖^2)≤1
  nonWeierstrass:∀sigma,WronskianFinite318.wronskian g (f sigma)
    (Periodic.qParam (width sigma) (tau sigma))≠0

variable {K}
@[expose] def Data.differentialLog {g i N:ℕ} (D:Data K g i N) (sigma:K→+*ℂ) : ℝ :=
  Real.log ‖deriv (fun z:ℂ=>1728*z^(D.width sigma)/D.G (z^(D.width sigma)))
    (Periodic.qParam (D.width sigma) (D.tau sigma))‖
@[expose] def Data.wronskianLog {g i N:ℕ} (D:Data K g i N) (sigma:K→+*ℂ) : ℝ :=
  Real.log ‖WronskianFinite318.wronskian g (D.f sigma)
    (Periodic.qParam (D.width sigma) (D.tau sigma))‖

theorem actual_archimedean_bounds {g i N:ℕ} (D:Data K g i N)
    (hg:2≤g) (hi:i≤g^3+1) (hN:1≤N) :
    -embeddingAverage K D.differentialLog≤absLogHeight₁ (1/((2:ℚ)^128+i))+9 ∧
    embeddingAverage K D.wronskianLog≤100*(g:ℝ)^2*Real.log (2*g*N) := by
  have hp (sigma:K→+*ℂ) := ActualCuspEstimates318.coordinate_estimates D.G
    D.holomorphicG D.boundG D.zeroG g i (D.width sigma) hg hi (D.width_pos sigma)
    N (by exact_mod_cast D.width_level sigma) (D.tau sigma) (D.fundamental sigma)
    (D.selected_value sigma)
  constructor
  · rw [←embedding_average_neg]
    apply embedding_average_le
    intro sigma
    exact (hp sigma).2.2.2.1
  · apply embedding_average_le
    intro sigma
    exact ActualWronskian318.local_wronskian_bound g (by omega) N
      (CuspRadius318.radius (D.width sigma)) (by exact_mod_cast hN)
      (hp sigma).2.1 (D.f sigma) (Periodic.qParam (D.width sigma) (D.tau sigma))
      (D.holomorphic sigma) (D.integrable sigma) (D.energy sigma)

end CuspArakelovData318
#print axioms CuspArakelovData318.embedding_average_le
#print axioms CuspArakelovData318.embedding_average_neg
#print axioms CuspArakelovData318.actual_archimedean_bounds
