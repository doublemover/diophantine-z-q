module
public import RationalGainChord318
public import NormalizedPolePoints318
public section
namespace ActualRationalGainChord318
open RationalGainChord318

/-- The elliptic cubic at a marked abscissa after one square scaling. -/
private theorem ordinate (β B v t e Y : ℚ) (hv : B=β*v^2)
    (hy : Y^2=β*(1-e)*(1+3*e)) :
    (B*v*t^3*Y)^2=(B*t^2)*(B*t^2-B*t^2*e)*(B*t^2+3*(B*t^2*e)) := by
  rw [mul_pow,hy,hv]
  ring

private theorem normalize (β B v t E Y : ℚ) (hB : B≠0) (hv : v≠0) (ht : t≠0)
    (hclass : B=β*v^2) (hy : Y^2=(B*t^2)*(B*t^2-E)*(B*t^2+3*E)) :
    (Y/(B*v*t^3))^2=β*(1-E/(B*t^2))*(1+3*(E/(B*t^2))) := by
  apply sub_eq_zero.mp
  calc
    (Y/(B*v*t^3))^2-β*(1-E/(B*t^2))*(1+3*(E/(B*t^2))) =
      (Y^2-(B*t^2)*(B*t^2-E)*(B*t^2+3*E))/(B*v*t^3)^2 := by
        field_simp [hB,hv,ht] <;> rw [hclass] <;> ring
    _ = 0 := by rw [hy]; simp

/-- Retains the literal original V and same free parameter at both abscissas. -/
theorem literal_iff {b β θ v z : ℚ} (hβ : 0<β) (hθ : 0<θ)
    (hv : v≠0) (hz : z≠0) (hB : 17*b=β*v^2) (hD : 1-b/17=θ*z^2)
    (hnβ : ∀ q : ℚ, β≠q^2) (hnθ : ∀ q : ℚ, θ≠q^2) :
    Nonempty (NormalizedPolePoints318.PointPair b) ↔ Search β θ := by
  rw [← exact_chord_iff hβ]
  let B := 17*b
  have hc : B=β*v^2 := hB
  have hBn : B≠0 := by rw [hc]; exact mul_ne_zero hβ.ne' (pow_ne_zero 2 hv)
  constructor
  · rintro ⟨P⟩
    let e := P.parameter/B
    let f := (P.parameter*(B^2*(1-b/17)))/(B*P.s^2)
    let y := P.y₁/(B*v)
    let t := P.y₂/(B*v*P.s^3)
    let w := e*B*z/P.s
    have hy : y^2=β*(1-e)*(1+3*e) := by
      simpa [y,e] using normalize β B v 1 P.parameter P.y₁ hBn hv (by norm_num) hc
        (by simpa [B] using P.first)
    have ht : t^2=β*(1-f)*(1+3*f) := by
      exact normalize β B v P.s _ P.y₂ hBn hv P.s_ne hc
        (by simpa only [mul_assoc] using P.second)
    have he : e≠0 := by
      intro h
      apply hnβ y
      simpa [h] using hy.symm
    have hw : w≠0 := div_ne_zero (mul_ne_zero (mul_ne_zero he hBn) hz) P.s_ne
    have hp : e*f=θ*w^2 := by
      dsimp [f,w,e]
      rw [hD]
      field_simp [hBn,P.s_ne] <;> ring
    refine ⟨e,f,y,t,w,?_,hw,hy,ht,hp⟩
    intro heq
    rw [← heq] at hp
    apply hnθ (e/w)
    field_simp [hw] <;> nlinarith [hp]
  · rintro ⟨e,f,y,t,w,hef,hw,hy,ht,hp⟩
    have hef0 : e*f≠0 := by rw [hp]; exact mul_ne_zero hθ.ne' (pow_ne_zero 2 hw)
    have he : e≠0 := fun h => hef0 (by rw [h,zero_mul])
    let S := e*B*z/w
    have hS : S≠0 := div_ne_zero (mul_ne_zero (mul_ne_zero he hBn) hz) hw
    have hscale : (B*e)*(B^2*(1-b/17))=B*S^2*f := by
      calc
        (B*e)*(B^2*(1-b/17)) = B^3*e*z^2*(θ*w^2)/w^2 := by
          rw [hD]; field_simp [hw] <;> ring
        _ = B*S^2*f := by rw [←hp]; dsimp [S]; field_simp [hw] <;> ring
    refine ⟨{ parameter := B*e, s := S, y₁ := B*v*y, y₂ := B*v*S^3*t,
              s_ne := hS, first := ?_, second := ?_ }⟩
    · simpa [B] using ordinate β B v 1 e y hc hy
    · have hpair : (B*v*S^3*t)^2 = (B*S^2)*(B*S^2-(B*e)*(B^2*(1-b/17)))*
        (B*S^2+3*((B*e)*(B^2*(1-b/17)))) := by
          rw [hscale]
          exact ordinate β B v S f t hc ht
      simpa only [B, mul_assoc] using hpair

end ActualRationalGainChord318
