module
public import EntireDoubleFourierTranslation318
public import PELOriginalThetaRealTorus318
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.MeasureTheory.Constructions.Pi
public section
noncomputable section
namespace EntireIntegerPeriodicRealTorus318
open QuaternionicRealPeriod318 PELOriginalThetaRealTorus318
open UnitAddTorus MeasureTheory Function
variable (f:ComplexVectors→ℂ) (hf:Continuous f)
    (h0:∀x y:ℂ,f ![x+1,y]=f ![x,y])
    (h1:∀x y:ℂ,f ![x,y+1]=f ![x,y])
lemma second_real_period(x:ℝ):Periodic (fun y:ℝ=>f ![(x:ℂ),(y:ℂ)]) 1:=by
  intro y
  simpa only [Complex.ofReal_add,Complex.ofReal_one] using h1 (x:ℂ) (y:ℂ)
@[expose] def innerLift(x:ℝ)(q:UnitAddCircle):ℂ:=(second_real_period f h1 x).lift q
lemma first_lift_period(q:UnitAddCircle):Periodic (fun x:ℝ=>innerLift f h1 x q) 1:=by
  intro x
  induction q using Quotient.inductionOn with
  | h y =>
    simpa only [innerLift,Periodic.lift_coe,Complex.ofReal_add,Complex.ofReal_one] using
      h0 (x:ℂ) (y:ℂ)
@[expose] def pairLift(q:UnitAddCircle×UnitAddCircle):ℂ:=
  (first_lift_period f h0 h1 q.2).lift q.1
lemma pair_evaluation(x y:ℝ):pairLift f h0 h1 ((x:UnitAddCircle),(y:UnitAddCircle))=
    f ![(x:ℂ),(y:ℂ)]:=rfl
lemma pair_continuous:Continuous (pairLift f h0 h1):=by
  have hm:= (QuotientAddGroup.isOpenQuotientMap_mk
    (N:=AddSubgroup.zmultiples (1:ℝ))).prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N:=AddSubgroup.zmultiples (1:ℝ)))
  rw [←hm.continuous_comp_iff]
  change Continuous (fun p:ℝ×ℝ=>f ![(p.1:ℂ),(p.2:ℂ)])
  apply hf.comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_one]
  · exact Complex.continuous_ofReal.comp continuous_fst
  · exact Complex.continuous_ofReal.comp continuous_snd
/-- Actual descent of ANY continuous integer-periodic function to the
real unit2torus. It is not chosen from the theta span. -/
@[expose] def torus:C(Torus,ℂ):=
  ⟨fun q=>pairLift f h0 h1 (q 0,q 1),
    (pair_continuous f hf h0 h1).comp ((continuous_apply 0).prodMk (continuous_apply 1))⟩
lemma real_evaluation(x:Fin 2→ℝ):torus f hf h0 h1 (torusPoint x)=f (realPoint x):=by
  change f ![(x 0:ℂ),(x 1:ℂ)]=f (realPoint x)
  congr 1
  ext i
  fin_cases i <;> rfl
end EntireIntegerPeriodicRealTorus318
