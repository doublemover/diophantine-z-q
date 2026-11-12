module
public import PELOriginalRealFanCover318
public section
noncomputable section
namespace RealOrientedCone318
open PELOriginalRealFanCover318
/-- The actual nonnegative span, not a formal cone label. -/
@[expose] def rayCone (P Q : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {W | ∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ W = a • P + b • Q}

theorem signed_cross_coordinates (o : ℝ) (P Q W : ℝ × ℝ)
    (h : 0 < o * realCross P Q) :
    W = ((o * realCross W Q) / (o * realCross P Q)) • P +
      ((o * realCross P W) / (o * realCross P Q)) • Q := by
  have hd := h.ne'
  apply Prod.ext
  · change W.1 = _ * P.1 + _ * Q.1
    field_simp [hd]
    simp only [realCross]
    ring
  · change W.2 = _ * P.2 + _ * Q.2
    field_simp [hd]
    simp only [realCross]
    ring

theorem sector_iff_rayCone (o : ℝ) (P Q W : ℝ × ℝ)
    (h : 0 < o * realCross P Q) :
    (0 ≤ o * realCross P W ∧ 0 ≤ o * realCross W Q) ↔ W ∈ rayCone P Q := by
  constructor
  · intro hW
    exact ⟨_,_,div_nonneg hW.2 h.le,div_nonneg hW.1 h.le,
      signed_cross_coordinates o P Q W h⟩
  · rintro ⟨a,b,ha,hb,rfl⟩
    have h1 : o * realCross P (a • P + b • Q) = b * (o * realCross P Q) := by
      simp only [realCross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring
    have h2 : o * realCross (a • P + b • Q) Q = a * (o * realCross P Q) := by
      simp only [realCross, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]
      ring
    rw [h1,h2]
    exact ⟨mul_nonneg hb h.le,mul_nonneg ha h.le⟩
/-- Positive rescaling of each generator under an injective real linear map
preserves the full nonnegative cone, in both directions. -/
theorem map_rayCone_iff (F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hF : Function.Injective F) (P Q P' Q' : ℝ × ℝ) (a b : ℝ)
    (ha : 0<a) (hb : 0<b) (hP : F P=a • P') (hQ : F Q=b • Q') (W : ℝ × ℝ) :
    W ∈ rayCone P Q ↔ F W ∈ rayCone P' Q' := by
  constructor
  · rintro ⟨x,y,hx,hy,rfl⟩
    refine ⟨x*a,y*b,mul_nonneg hx ha.le,mul_nonneg hy hb.le,?_⟩
    simp only [map_add,map_smul,hP,hQ,smul_smul]
  · rintro ⟨x,y,hx,hy,hW⟩
    refine ⟨x/a,y/b,div_nonneg hx ha.le,div_nonneg hy hb.le,?_⟩
    apply hF
    rw [map_add,map_smul,map_smul,hP,hQ,smul_smul,smul_smul]
    simpa only [div_mul_cancel₀ _ ha.ne',div_mul_cancel₀ _ hb.ne'] using hW
end RealOrientedCone318
