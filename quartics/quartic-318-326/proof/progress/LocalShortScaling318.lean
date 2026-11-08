module
public import LocalHolomorphicSquareRoot318
public section
noncomputable section
namespace LocalShortScaling318
open Filter Topology
set_option maxHeartbeats 0

@[expose] def ratio (A B C D : ℂ → ℂ) (z : ℂ) : ℂ := (D z/B z)/(C z/A z)

lemma ratio_of_scaling (A B C D : ℂ → ℂ) (z : ℂ) (u : ℂˣ)
    (hA : A z ≠ 0) (hB : B z ≠ 0)
    (hC : C z=(u:ℂ)^4*A z) (hD : D z=(u:ℂ)^6*B z) :
    ratio A B C D z=(u:ℂ)^2 := by
  rw [ratio,hC,hD,mul_div_cancel_right₀ _ hB,mul_div_cancel_right₀ _ hA]
  field_simp [Units.ne_zero u]

/-- Pointwise short-model scalings of analytic coefficient families yield
an actual holomorphic scaling in a neighborhood of any nondegenerate point. -/
theorem exists_local_scaling (A B C D : ℂ → ℂ) (a : ℂ)
    (hA : AnalyticAt ℂ A a) (hB : AnalyticAt ℂ B a)
    (hC : AnalyticAt ℂ C a) (hD : AnalyticAt ℂ D a)
    (hA0 : A a ≠ 0) (hB0 : B a ≠ 0) (u0 : ℂˣ)
    (hu4 : C a=(u0:ℂ)^4*A a) (hu6 : D a=(u0:ℂ)^6*B a)
    (hex : ∀ᶠ z in 𝓝 a, ∃ u : ℂˣ, C z=(u:ℂ)^4*A z ∧ D z=(u:ℂ)^6*B z) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ u a=u0 ∧
      ∀ᶠ z in 𝓝 a, u z≠0 ∧ C z=u z^4*A z ∧ D z=u z^6*B z := by
  have hC0 : C a ≠ 0 := by rw [hu4]; exact mul_ne_zero (pow_ne_zero 4 (Units.ne_zero u0)) hA0
  have hr : AnalyticAt ℂ (ratio A B C D) a :=
    (hD.div hB hB0).div (hC.div hA hA0) (div_ne_zero hC0 hA0)
  have hra := ratio_of_scaling A B C D a u0 hA0 hB0 hu4 hu6
  have hr0 : ratio A B C D a ≠ 0 := by rw [hra]; exact pow_ne_zero 2 (Units.ne_zero u0)
  obtain ⟨u,hu,hu0,hu2⟩ := LocalHolomorphicSquareRoot318.exists_local_root
    (ratio A B C D) a u0 hr hr0 hra.symm
  refine ⟨u,hu,hu0,?_⟩
  filter_upwards [hex,hA.continuousAt.eventually_ne hA0,hB.continuousAt.eventually_ne hB0]
    with z hz hAz hBz
  obtain ⟨v,hv4,hv6⟩ := hz
  have he : u z^2=(v:ℂ)^2 := (hu2 z).trans (ratio_of_scaling A B C D z v hAz hBz hv4 hv6)
  refine ⟨?_,?_,?_⟩
  · intro hz0
    have hv0 : (v:ℂ)^2=0 := by simpa [hz0] using he.symm
    exact pow_ne_zero 2 (Units.ne_zero v) hv0
  · rw [hv4,show u z^4=(v:ℂ)^4 by
      calc u z^4=(u z^2)^2 := by ring
           _=((v:ℂ)^2)^2 := by rw [he]
           _=(v:ℂ)^4 := by ring]
  · rw [hv6,show u z^6=(v:ℂ)^6 by
      calc u z^6=(u z^2)^3 := by ring
           _=((v:ℂ)^2)^3 := by rw [he]
           _=(v:ℂ)^6 := by ring]

end LocalShortScaling318
