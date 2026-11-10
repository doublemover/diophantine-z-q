module
public import EntirePeriodicHorizontalIntegral318
public import QuaternionicRealPeriod318
public import Mathlib.MeasureTheory.Integral.Prod
public section
noncomputable section
namespace EntirePeriodicDoubleIntegral318
open QuaternionicRealPeriod318 Complex MeasureTheory intervalIntegral Set
variable (f:ComplexVectors→ℂ) (hf:Differentiable ℂ f)
    (h0:∀x y:ℂ,f ![x+1,y]=f ![x,y])
    (h1:∀x y:ℂ,f ![x,y+1]=f ![x,y])
lemma first_entire(y:ℂ):Differentiable ℂ (fun x:ℂ=>f ![x,y]):=by
  apply hf.comp
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · simpa only [Matrix.cons_val_zero] using (differentiable_id:Differentiable ℂ (fun x:ℂ=>x))
  · simpa only [Matrix.cons_val_one] using (differentiable_const y:Differentiable ℂ (fun _:ℂ=>y))
lemma second_entire(x:ℂ):Differentiable ℂ (fun y:ℂ=>f ![x,y]):=by
  apply hf.comp
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · simpa only [Matrix.cons_val_zero] using (differentiable_const x:Differentiable ℂ (fun _:ℂ=>x))
  · simpa only [Matrix.cons_val_one] using (differentiable_id:Differentiable ℂ (fun y:ℂ=>y))

/-- Fubini on a genuine compact rectangle, with integrability proved
from continuity; no formal interchange of the two period integrals. -/
lemma swap_continuous (g:ℝ→ℝ→ℂ) (hg:Continuous g.uncurry):
    (∫y:ℝ in 0..1,∫x:ℝ in 0..1,g y x)=
      ∫x:ℝ in 0..1,∫y:ℝ in 0..1,g y x:=by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  have hi:=hg.continuousOn.integrableOn_isCompact
    (isCompact_Icc.prod isCompact_Icc : IsCompact (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) 1))
  apply hi.mono_set
  simp only [uIoc_of_le (by norm_num:(0:ℝ)≤1)]
  exact Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
@[expose] def periodIntegral (w:ComplexVectors):ℂ:=
  ∫y:ℝ in 0..1,∫x:ℝ in 0..1,f ![(x:ℂ)+w 0,(y:ℂ)+w 1]

/-- Moving the ENTIRE real two-torus by ANY complex vector leaves the
integral of an actual entire doubly-periodic function unchanged. Both
coordinate shifts and the intervening Fubini interchange are produced. -/
theorem period_shift (w:ComplexVectors):periodIntegral f w=periodIntegral f 0:=by
  have hx(y:ℝ):
      (∫x:ℝ in 0..1,f ![(x:ℂ)+w 0,(y:ℂ)+w 1])=
        ∫x:ℝ in 0..1,f ![(x:ℂ),(y:ℂ)+w 1]:=
    EntirePeriodicHorizontalIntegral318.complex_shift
      (fun x:ℂ=>f ![x,(y:ℂ)+w 1]) (first_entire f hf _) (fun x=>h0 x _) (w 0)
  have hy(x:ℝ):
      (∫y:ℝ in 0..1,f ![(x:ℂ),(y:ℂ)+w 1])=
        ∫y:ℝ in 0..1,f ![(x:ℂ),(y:ℂ)]:=
    EntirePeriodicHorizontalIntegral318.complex_shift
      (fun y:ℂ=>f ![(x:ℂ),y]) (second_entire f hf _) (h1 (x:ℂ)) (w 1)
  have hc:Continuous (fun p:ℝ×ℝ=>f ![(p.2:ℂ),(p.1:ℂ)+w 1]):=by
    apply hf.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    · exact Complex.continuous_ofReal.comp continuous_snd
    · exact (Complex.continuous_ofReal.comp continuous_fst).add continuous_const
  have hc0:Continuous (fun p:ℝ×ℝ=>f ![(p.2:ℂ),(p.1:ℂ)]):=by
    apply hf.continuous.comp
    apply continuous_pi
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
    · exact Complex.continuous_ofReal.comp continuous_snd
    · exact Complex.continuous_ofReal.comp continuous_fst
  simp only [periodIntegral,Pi.zero_apply,add_zero]
  simp_rw [hx]
  rw [swap_continuous (fun y x:ℝ=>f ![(x:ℂ),(y:ℂ)+w 1]) hc]
  simp_rw [hy]
  exact (swap_continuous (fun y x:ℝ=>f ![(x:ℂ),(y:ℂ)]) hc0).symm
end EntirePeriodicDoubleIntegral318
