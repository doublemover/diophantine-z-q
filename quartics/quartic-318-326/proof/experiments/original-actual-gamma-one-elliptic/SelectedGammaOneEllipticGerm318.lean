module
public import SelectedGammaOneEllipticAction318
public import SelectedGammaOneCuspGerm318
public section
noncomputable section

open scoped Topology

namespace SelectedGammaOneEllipticGerm318

/-- The actual Cayley coordinate with the elliptic fixed point a and its
conjugate fixed point b. -/
@[expose] def cayley (a b z : ℂ) : ℂ := (z-a)/(z-b)

private theorem mobius_sub_root (z t r : ℂ) (hz : z+t ≠ 0)
    (hr : r*r+t*r+1=0) : (-(1:ℂ))/(z+t)-r = (-r)*(z-r)/(z+t) := by
  apply (eq_div_iff hz).mpr
  rw [sub_mul,div_mul_cancel₀ _ hz]
  linear_combination -hr

/-- Simultaneously applies to the literal modular transformations
S:z↦−1/z and ST:z↦−1/(z+1). The Cayley multiplier is exactly a/b. -/
theorem cayley_rotation (z t a b : ℂ) (hz : z+t ≠ 0)
    (hb : b ≠ 0) (hzb : z-b ≠ 0)
    (haq : a*a+t*a+1=0) (hbq : b*b+t*b+1=0) :
    cayley a b ((-(1:ℂ))/(z+t)) = (a/b)*cayley a b z := by
  simp only [cayley, mobius_sub_root z t a hz haq, mobius_sub_root z t b hz hbq]
  rw [div_div_div_cancel_right₀ hz]
  field_simp [hb,hzb] <;> ring

/-- At i and −i, the literal S action is multiplication by −1
in the elliptic fixed-point coordinate. -/
theorem S_rotation (z : ℂ) (hz : z ≠ 0) (hzi : z-(-Complex.I) ≠ 0) :
    cayley Complex.I (-Complex.I) ((-(1:ℂ))/z) =
      -cayley Complex.I (-Complex.I) z := by
  have hqi : Complex.I*Complex.I+0*Complex.I+1=0 := by
    rw [← pow_two,Complex.I_sq] <;> ring
  have hqni : (-Complex.I)*(-Complex.I)+0*(-Complex.I)+1=0 := by
    simpa only [neg_mul_neg,zero_mul,add_zero] using hqi
  have hratio : Complex.I/(-Complex.I) = -1 := by
    field_simp [Complex.I_ne_zero] <;> ring
  simpa only [add_zero,hratio,neg_one_mul] using
    cayley_rotation z 0 Complex.I (-Complex.I) (by simpa only [add_zero] using hz)
      (neg_ne_zero.mpr Complex.I_ne_zero) hzi hqi hqni

/-- At the actual primitive cube root ρ and conjugate ρ², the literal ST
action multiplies the Cayley coordinate by ρ², not by an arbitrary scalar. -/
theorem U_rotation (z ρ : ℂ) (hρ : ρ^2+ρ+1=0)
    (hz : z+1 ≠ 0) (hzb : z-ρ^2 ≠ 0) :
    cayley ρ (ρ^2) ((-(1:ℂ))/(z+1)) = (ρ^2)*cayley ρ (ρ^2) z := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    simp [h] at hρ
  have hρ3 : ρ^3=1 := by linear_combination (ρ-1)*hρ
  have hρ4 : ρ^4=ρ := by
    calc
      _ = ρ^3*ρ := by ring
      _ = _ := by rw [hρ3,one_mul]
  have hqs : (ρ^2)*(ρ^2)+1*(ρ^2)+1=0 := by
    linear_combination hρ4+hρ
  have hρ2 : ρ^2 ≠ 0 := pow_ne_zero _ hρ0
  have hratio : ρ/(ρ^2)=ρ^2 := (div_eq_iff hρ2).mpr (by linear_combination -hρ4)
  simpa only [hratio] using
    cayley_rotation z 1 ρ (ρ^2) hz hρ2 hzb (by simpa only [pow_two,one_mul] using hρ) hqs

/-- The compact comparison supplies genuine chart equalities, not the
orders of the source functions. J0 and J1728 are the two restrictions
of the actual J; the second displayed germ is the literal J−1728. -/
theorem actual_elliptic_orders (J0 J1728 F0 F1728 : ℂ → ℂ)
    (hF0 : AnalyticAt ℂ F0 0) (hF1728 : AnalyticAt ℂ F1728 0)
    (simple0 : analyticOrderAt F0 0 = 1) (simple1728 : analyticOrderAt F1728 0 = 1)
    (chart0 : J0 =ᶠ[𝓝 0] (F0 ∘ fun z : ℂ => z^3))
    (chart1728 : (fun z => J1728 z-1728) =ᶠ[𝓝 0] (F1728 ∘ fun z : ℂ => z^2)) :
    analyticOrderAt J0 0 = 3 ∧ analyticOrderAt (fun z => J1728 z-1728) 0 = 2 := by
  exact ⟨(analyticOrderAt_congr chart0).trans
      (SelectedGammaOneCuspGerm318.width_order 3 (by decide) F0 hF0 simple0),
    (analyticOrderAt_congr chart1728).trans
      (SelectedGammaOneCuspGerm318.width_order 2 (by decide) F1728 hF1728 simple1728)⟩

end SelectedGammaOneEllipticGerm318

#print axioms SelectedGammaOneEllipticGerm318.S_rotation
#print axioms SelectedGammaOneEllipticGerm318.U_rotation
#print axioms SelectedGammaOneEllipticGerm318.actual_elliptic_orders
