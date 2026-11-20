module
public import NormalizedPolePoints318
public import OriginalScalarAuxiliaryCut318
public section

namespace OriginalScalarAuxiliaryPointPair318
open OriginalScalarAuxiliaryCut318

@[expose] def r (β t : ℚ) : ℚ := β*t^2+3
@[expose] def y (β t : ℚ) : ℚ := β*(r β t)*(2*(3-β*t^2))*(4*β*t)

lemma cubic (β t : ℚ) :
    (y β t)^2=(β*(r β t)^2)*(β*(r β t)^2-parameter β t)*
      (β*(r β t)^2+3*parameter β t) := by
  simp only [y,r,parameter,F1,F9]
  ring

lemma r_ne {β t : ℚ} (hβ : 0 < β) : r β t ≠ 0 := by
  unfold r
  positivity

/-- Direct original PointPair at the same fixed b. Both homogeneity scales
are explicit. The coordinate-only inputs do not invoke any group or rank. -/
noncomputable def of_cut (b β θ c e t k : ℚ) (hb : b ≠ 0)
    (hβ : 0 < β) (hc : c ≠ 0) (he0 : e ≠ 0) (hk : k ≠ 0)
    (hB : b/17=D β c) (hδ : δ β c=θ*e^2)
    (hd : den β c t ≠ 0) (hcut : G β c t=k^2*F9 β t) :
    NormalizedPolePoints318.PointPair b := by
  let t' := comp β c t
  let w : ℚ := e*k/(den β c t)^2
  let c₀ : ℚ := 17*c
  let d₀ : ℚ := (17*b)*e
  let L : ℚ := c₀/r β t
  have hw : w ≠ 0 := div_ne_zero (mul_ne_zero he0 hk) (pow_ne_zero 2 hd)
  have hr : r β t ≠ 0 := r_ne hβ
  have hr' : r β t' ≠ 0 := r_ne hβ
  have hd₀ : d₀ ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hb) he0
  have hB' : 17*b=β*c₀^2 := by
    dsimp only [c₀]
    unfold D at hB
    linear_combination 289*hB
  have hV : (17*b)^2*(1-b/17)=θ*d₀^2 := by
    have he : 1-b/17=θ*e^2 := by simpa only [hB,δ] using hδ
    rw [he]
    dsimp only [d₀]
    ring
  have hC : parameter β t'=(parameter β t*θ)*w^2 :=
    mobius_parameter β θ c e t k hδ hd hcut
  have hscale : (β*r β t^2)*L^2=17*b := by
    rw [hB']
    dsimp only [L]
    field_simp [hr] <;> ring
  let s : ℚ := (r β t'*d₀)/(r β t*w)
  let L' : ℚ := L*d₀/w
  have hx : (β*r β t'^2)*L'^2=(17*b)*s^2 := by
    rw [hB']
    dsimp only [L',L,s]
    field_simp [hr,hw] <;> ring
  have hN : parameter β t'*L'^2=(parameter β t*L^2)*((17*b)^2*(1-b/17)) := by
    rw [hC,hV]
    dsimp only [L']
    field_simp [hw] <;> ring
  refine ⟨parameter β t*L^2,s,y β t*L^3,y β t'*L'^3,?_,?_,?_⟩
  · exact div_ne_zero (mul_ne_zero hr' hd₀) (mul_ne_zero hr hw)
  · rw [← hscale]
    linear_combination L^6*cubic β t
  · rw [← hx,← hN]
    linear_combination L'^6*cubic β t'

/-- Input is a rational affine point of the same E_c, whose actual x is
β*r₀². Only the literal open-chart exclusions are required. -/
noncomputable def of_aux (b β θ c e r₀ X Y : ℚ) (hb : b ≠ 0)
    (hβ : 0 < β) (hc : c ≠ 0) (he0 : e ≠ 0) (hr₀ : r₀ ≠ 0)
    (hB : b/17=D β c) (hδ : δ β c=θ*e^2)
    (hX : X=β*r₀^2) (hY : Y^2=aux β c X)
    (ha : quad β c (r₀/3) ≠ 0)
    (hd : den β c ((Y/(9*β*(r₀/3))+8*β*c)/quad β c (r₀/3)) ≠ 0) :
    NormalizedPolePoints318.PointPair b := by
  let k : ℚ := r₀/3
  let H : ℚ := Y/(9*β*k)
  let t : ℚ := (H+8*β*c)/quad β c k
  have hk : k ≠ 0 := div_ne_zero hr₀ (by norm_num)
  have hx : X=9*β*k^2 := by
    rw [hX]
    dsimp only [k]
    ring
  rw [hx] at hY
  have hH := aux_discriminant β c k Y (ne_of_gt hβ) hk hY
  exact of_cut b β θ c e t k hb hβ hc he0 hk hB hδ hd
    (reverse_cut β c k H ha hH)

end OriginalScalarAuxiliaryPointPair318
#print axioms OriginalScalarAuxiliaryPointPair318.of_cut
#print axioms OriginalScalarAuxiliaryPointPair318.of_aux
