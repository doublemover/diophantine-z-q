module
public import ComplexSphereFourPointNormalization318
public section
noncomputable section
namespace ComplexSphereImaginaryNormalization318
open Set
open scoped OnePoint
open ComplexSphereAffineNormalization318 ComplexSphereFourPointNormalization318 SphereInversion318

/-- The extended imaginary axis in the independent standard sphere. -/
@[expose] def OnAxis (p:OnePoint ℂ) : Prop:=p=∞ ∨ ∃z:ℂ,z.re=0 ∧ (z:OnePoint ℂ)=p
lemma coe_onAxis (z:ℂ) : OnAxis (z:OnePoint ℂ) ↔ z.re=0 := by
  constructor
  · rintro (h|⟨w,hw,he⟩)
    · exact False.elim (OnePoint.coe_ne_infty z h)
    · exact (OnePoint.coe_injective he) ▸ hw
  · intro h; exact Or.inr ⟨z,h,rfl⟩
lemma inversion_onAxis (p:OnePoint ℂ) (hp:OnAxis p) : OnAxis (inversion p) := by
  rcases hp with rfl|⟨z,hz,rfl⟩
  · rw [inversion_infty]; exact (coe_onAxis 0).mpr (by simp)
  · by_cases h0:z=0
    · rw [h0,inversion_zero]; exact Or.inl rfl
    · rw [inversion_coe h0]
      exact (coe_onAxis _).mpr (by rw [Complex.inv_re,hz,zero_div])
lemma translation_onAxis (a:ℂ) (ha:a.re=0) (p:OnePoint ℂ) (hp:OnAxis p) :
    OnAxis (affineSphere 1 (-a) one_ne_zero p) := by
  rcases hp with rfl|⟨z,hz,rfl⟩
  · rw [affineSphere_infty]; exact Or.inl rfl
  · rw [affineSphere_coe]
    exact (coe_onAxis _).mpr (by simp [hz,ha])
lemma pole_onAxis (a p:OnePoint ℂ) (ha:OnAxis a) (hp:OnAxis p) :
    OnAxis (poleCoordinate a p) := by
  rcases ha with rfl|⟨z,hz,rfl⟩
  · exact hp
  · exact inversion_onAxis _ (translation_onAxis z hz p hp)

/-- The SAME chosen finite coordinates stay on the axis after pole change. -/
lemma finiteCoordinate_real_zero (p:Fin 4→OnePoint ℂ) (hp:Function.Injective p)
    (haxis:∀j,OnAxis (p j)) (j:Fin 3) : (finiteCoordinate p hp j).re=0 := by
  apply (coe_onAxis _).mp
  rw [finiteCoordinate_spec]
  exact pole_onAxis _ _ (haxis 0) (haxis j.succ)

/-- Three-point normalization of four distinct points on the extended
imaginary axis has REAL cross-ratio, including a possible point at infinity.
No choice of an unrelated normalization or parameter is made. -/
theorem parameter_im_zero (p:Fin 4→OnePoint ℂ) (hp:Function.Injective p)
    (haxis:∀j,OnAxis (p j)) : (parameter p hp).im=0 := by
  have h0:=finiteCoordinate_real_zero p hp haxis 0
  have h1:=finiteCoordinate_real_zero p hp haxis 1
  have h2:=finiteCoordinate_real_zero p hp haxis 2
  simp only [parameter,Complex.div_im,Complex.sub_re,h0,h1,h2,sub_self,
    zero_mul,mul_zero,sub_zero,zero_div]
end ComplexSphereImaginaryNormalization318
