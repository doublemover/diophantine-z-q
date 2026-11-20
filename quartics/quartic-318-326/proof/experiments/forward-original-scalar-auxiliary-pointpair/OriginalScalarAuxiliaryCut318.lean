module
public import Mathlib.Tactic
public section

namespace OriginalScalarAuxiliaryCut318

@[expose] def D (β c : ℚ) : ℚ := β*c^2
@[expose] def δ (β c : ℚ) : ℚ := 1-D β c
@[expose] def F1 (β t : ℚ) : ℚ := β*t^2-1
@[expose] def F9 (β t : ℚ) : ℚ := β*t^2-9
@[expose] def den (β c t : ℚ) : ℚ := 1+β*c*t
@[expose] def comp (β c t : ℚ) : ℚ := (t+c)/den β c t
@[expose] def G (β c t : ℚ) : ℚ := β*(t+c)^2-9*(den β c t)^2
@[expose] def quad (β c k : ℚ) : ℚ := β*(1-9*D β c-k^2)
@[expose] def aux (β c X : ℚ) : ℚ :=
  X*(X^2+β*(82*D β c-18)*X+81*β^2*(δ β c)^2)
@[expose] def parameter (β t : ℚ) : ℚ := β*F1 β t*F9 β t

lemma reverse_cut (β c k H : ℚ) (ha : quad β c k ≠ 0)
    (hH : H^2=β*(9*k^4+(82*D β c-18)*k^2+9*(δ β c)^2)) :
    let t := (H+8*β*c)/quad β c k
    G β c t=k^2*F9 β t := by
  dsimp only
  apply mul_right_cancel₀ (pow_ne_zero 2 ha)
  calc
    G β c ((H+8*β*c)/quad β c k)*(quad β c k)^2 =
        β*(H+8*β*c+c*quad β c k)^2-
        9*(quad β c k+β*c*(H+8*β*c))^2 := by
          simp only [G, den]
          field_simp [ha] <;> ring
    _ = k^2*(F9 β ((H+8*β*c)/quad β c k)*(quad β c k)^2) := by
      have hF : F9 β ((H+8*β*c)/quad β c k)*(quad β c k)^2 =
          β*(H+8*β*c)^2-9*(quad β c k)^2 := by
        simp only [F9]
        field_simp [ha] <;> ring
      rw [hF]
      simp only [quad,D,δ] at hH ⊢
      linear_combination (β*(1-9*(β*c^2)-k^2))*hH
    _ = (k^2*F9 β ((H+8*β*c)/quad β c k))*(quad β c k)^2 := by ring

lemma aux_discriminant (β c k Y : ℚ) (hβ : β ≠ 0) (hk : k ≠ 0)
    (hY : Y^2=aux β c (9*β*k^2)) :
    (Y/(9*β*k))^2=β*(9*k^4+(82*D β c-18)*k^2+9*(δ β c)^2) := by
  rw [div_pow,hY]
  simp only [aux]
  field_simp [hβ,hk] <;> ring

lemma mobius_parameter (β θ c e t k : ℚ) (he : δ β c=θ*e^2)
    (hd : den β c t ≠ 0) (hg : G β c t=k^2*F9 β t) :
    parameter β (comp β c t)=
      (parameter β t*θ)*(e*k/(den β c t)^2)^2 := by
  have h1 : F1 β (comp β c t)=(δ β c)*F1 β t/(den β c t)^2 := by
    simp only [F1,comp,D,δ,den] at hd ⊢
    field_simp [hd] <;> ring
  have h9 : F9 β (comp β c t)=G β c t/(den β c t)^2 := by
    simp only [F9,comp,G,den] at hd ⊢
    field_simp [hd] <;> ring
  rw [parameter,h1,h9,he,hg,parameter]
  field_simp [hd] <;> ring

end OriginalScalarAuxiliaryCut318
