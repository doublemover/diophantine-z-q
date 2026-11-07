module
public import PadicIntEvaluation318
public import IntegralFormalAddition318
public section
namespace EvaluatedAddition318
open PadicIntEvaluation318
variable (p : ℕ) [Fact p.Prime]
noncomputable section
attribute [local instance] DiscreteTopology.instContinuousSMul

@[expose] def toPadic : Coeff p →+* ℚ_[p] := PadicInt.Coe.ringHom.comp (coefficientMap p)
theorem toPadic_injective : Function.Injective (toPadic p) := by
  intro a b h
  exact Subtype.ext h

/-- Evaluating the proved formal identity gives actual convergent addition.
The two hypotheses are exact coefficient bindings, not an assumed logarithm law. -/
theorem evaluated_addition (D : Coeff p) (L V : PowerSeries (Coeff p))
    (hL : L.map (toPadic p)=GenericFormalDifferential318.integral (toPadic p D))
    (hV : V.map (toPadic p)=GenericFormalDifferential318.branch (toPadic p D))
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    PowerSeries.eval₂ (coefficientMap p)
      (MvPowerSeries.eval₂ (coefficientMap p) z (IntegralFormalAddition318.f D V)) L =
    PowerSeries.eval₂ (coefficientMap p) (z 0) L+
      PowerSeries.eval₂ (coefficientMap p) (z 1) L := by
  have hf := IntegralFormalAddition318.formal_addition (toPadic p) (toPadic_injective p) D L V hL hV
  let e := MvPowerSeries.aeval (R:=Coeff p) (point_hasEval p z hz)
  have hh := congrArg e hf
  rw [map_add] at hh
  dsimp only [e] at hh
  simp only [MvPowerSeries.coe_aeval] at hh
  change MvPowerSeries.eval₂ (coefficientMap p) z (L.subst (IntegralFormalAddition318.f D V))=
    MvPowerSeries.eval₂ (coefficientMap p) z (L.subst IntegralFormalAddition318.x)+
    MvPowerSeries.eval₂ (coefficientMap p) z (L.subst IntegralFormalAddition318.a) at hh
  rw [evaluation_subst p L _ (IntegralFormalAddition318.f_zero D V),
    evaluation_subst p L _ IntegralFormalAddition318.x_zero,
    evaluation_subst p L _ IntegralFormalAddition318.a_zero] at hh
  · simpa only [IntegralFormalAddition318.x,IntegralFormalAddition318.a,MvPowerSeries.eval₂_X] using hh
  all_goals exact hz

theorem norm_lt_one_of_hasEval (x : ℤ_[p]) (hx : PowerSeries.HasEval x) : ‖x‖<1 := by
  have hh := continuous_norm.tendsto (0:ℤ_[p]) |>.comp hx
  have ht : Filter.Tendsto (fun n : ℕ => ‖x‖^n) Filter.atTop (nhds (0:ℝ)) := by
    simpa only [Function.comp_def,norm_pow,norm_zero] using hh
  simpa only [abs_of_nonneg (norm_nonneg x)] using tendsto_pow_atTop_nhds_zero_iff.mp ht

open MvPowerSeries.WithPiTopology in
/-- Zero-constant integral formal series evaluate inside the maximal ideal. -/
theorem evaluation_zero_small (g : MvPowerSeries (Fin 2) (Coeff p))
    (hg : MvPowerSeries.constantCoeff g=0) (x : Fin 2 → ℤ_[p]) (hx : ∀i,‖x i‖<1) :
    ‖MvPowerSeries.eval₂ (coefficientMap p) x g‖<1 := by
  let e := MvPowerSeries.aeval (R:=Coeff p) (point_hasEval p x hx)
  have hg' := (PowerSeries.HasSubst.of_constantCoeff_zero hg).hasEval
  have he : Continuous e := MvPowerSeries.continuous_aeval (point_hasEval p x hx)
  have ht := hg'.map (φ:=e.toRingHom) he
  apply norm_lt_one_of_hasEval p
  change PowerSeries.HasEval (e g) at ht
  dsimp only [e] at ht
  rw [MvPowerSeries.coe_aeval] at ht
  exact ht


open MvPowerSeries.WithPiTopology in
theorem evaluation_zero_small_univariate (g : PowerSeries (Coeff p))
    (hg : PowerSeries.constantCoeff g=0) (x : ℤ_[p]) (hx : ‖x‖<1) :
    ‖PowerSeries.eval₂ (coefficientMap p) x g‖<1 := by
  let e := PowerSeries.aeval (R:=Coeff p) (hasEval_of_norm_lt_one p x hx)
  have hg' := (PowerSeries.HasSubst.of_constantCoeff_zero' hg).hasEval
  have he : Continuous e := PowerSeries.continuous_aeval (hasEval_of_norm_lt_one p x hx)
  have ht := hg'.map (φ:=e.toRingHom) he
  apply norm_lt_one_of_hasEval p
  change PowerSeries.HasEval (e g) at ht
  dsimp only [e] at ht
  rw [PowerSeries.coe_aeval] at ht
  exact ht

theorem branch_constant (D : Coeff p) (V : PowerSeries (Coeff p))
    (hV : V.map (toPadic p)=GenericFormalDifferential318.branch (toPadic p D)) :
    PowerSeries.constantCoeff V=1 := by
  apply toPadic_injective p
  have h := congrArg (PowerSeries.coeff 0) hV
  simpa only [PowerSeries.coeff_map,PowerSeries.coeff_zero_eq_constantCoeff_apply,
    GenericFormalDifferential318.branch_constant,map_one] using h

theorem branch_square (D : Coeff p) (V : PowerSeries (Coeff p))
    (hV : V.map (toPadic p)=GenericFormalDifferential318.branch (toPadic p D)) :
    V^2=1-PowerSeries.C D*PowerSeries.X^4 := by
  apply PowerSeries.map_injective (toPadic p) (toPadic_injective p)
  simpa only [map_pow,map_sub,map_one,map_mul,PowerSeries.map_C,PowerSeries.map_X,hV,
    GenericFormalDifferential318.argument] using GenericFormalDifferential318.branch_square (toPadic p D)

theorem evaluated_branch (D : Coeff p) (V : PowerSeries (Coeff p))
    (hV : V.map (toPadic p)=GenericFormalDifferential318.branch (toPadic p D))
    (x : ℤ_[p]) (hx : ‖x‖<1) :
    (PowerSeries.eval₂ (coefficientMap p) x V)^2=1-coefficientMap p D*x^4 ∧
    ‖PowerSeries.eval₂ (coefficientMap p) x V-1‖<1 := by
  let e := PowerSeries.aeval (R:=Coeff p) (hasEval_of_norm_lt_one p x hx)
  have heval (z : PowerSeries (Coeff p)) : e z=PowerSeries.eval₂ (coefficientMap p) x z := by
    exact congrFun (PowerSeries.coe_aeval (hasEval_of_norm_lt_one p x hx)) z
  constructor
  · have h := congrArg e (branch_square p D V hV)
    rw [map_pow,map_sub,map_one,map_mul,map_pow] at h
    simpa only [heval,PowerSeries.eval₂_C,PowerSeries.eval₂_X] using h
  · have hg : PowerSeries.constantCoeff (V-1)=0 := by rw [map_sub,branch_constant p D V hV,map_one,sub_self]
    have hh := evaluation_zero_small_univariate p (V-1) hg x hx
    have he : PowerSeries.eval₂ (coefficientMap p) x (V-1)=PowerSeries.eval₂ (coefficientMap p) x V-1 := by
      rw [←heval,map_sub,map_one,heval]
    rwa [he] at hh


theorem evaluated_parameter (D : Coeff p) (V : PowerSeries (Coeff p))
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    ((MvPowerSeries.eval₂ (coefficientMap p) z (IntegralFormalAddition318.f D V) : ℤ_[p]) : ℚ_[p]) =
    ((z 0:ℚ_[p])*(PowerSeries.eval₂ (coefficientMap p) (z 1) V:ℤ_[p])+
      (z 1:ℚ_[p])*(PowerSeries.eval₂ (coefficientMap p) (z 0) V:ℤ_[p])) /
      (1+toPadic p D*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2) := by
  let e := MvPowerSeries.aeval (R:=Coeff p) (point_hasEval p z hz)
  let r : MvPowerSeries (Fin 2) (Coeff p) →+* ℚ_[p] := PadicInt.Coe.ringHom.comp e.toRingHom
  have er (F : MvPowerSeries (Fin 2) (Coeff p)) : r F=
      ((MvPowerSeries.eval₂ (coefficientMap p) z F : ℤ_[p]):ℚ_[p]) := by
    dsimp only [r,RingHom.comp_apply]
    change (e F:ℚ_[p])=_
    dsimp only [e]
    rw [MvPowerSeries.coe_aeval]
    rfl
  have rx : r IntegralFormalAddition318.x=(z 0:ℚ_[p]) := by
    rw [er]; simp only [IntegralFormalAddition318.x,MvPowerSeries.eval₂_X]
  have ra : r IntegralFormalAddition318.a=(z 1:ℚ_[p]) := by
    rw [er]; simp only [IntegralFormalAddition318.a,MvPowerSeries.eval₂_X]
  have rvx : r (IntegralFormalAddition318.v V IntegralFormalAddition318.x)=
      (PowerSeries.eval₂ (coefficientMap p) (z 0) V : ℤ_[p]) := by
    rw [er,IntegralFormalAddition318.v,evaluation_subst p V _ IntegralFormalAddition318.x_zero z hz]
    simp only [IntegralFormalAddition318.x,MvPowerSeries.eval₂_X]
  have rva : r (IntegralFormalAddition318.v V IntegralFormalAddition318.a)=
      (PowerSeries.eval₂ (coefficientMap p) (z 1) V : ℤ_[p]) := by
    rw [er,IntegralFormalAddition318.v,evaluation_subst p V _ IntegralFormalAddition318.a_zero z hz]
    simp only [IntegralFormalAddition318.a,MvPowerSeries.eval₂_X]
  have rq : r (IntegralFormalAddition318.q D)=1+toPadic p D*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2 := by
    rw [IntegralFormalAddition318.q,map_add,map_one,map_mul,map_mul,map_pow,map_pow,rx,ra]
    congr 3
    rw [er,MvPowerSeries.eval₂_C]
    rfl
  have hinv : r ((IntegralFormalAddition318.q D).invOfUnit 1)*r (IntegralFormalAddition318.q D)=1 := by
    rw [←map_mul,MvPowerSeries.invOfUnit_mul _ 1 (by simp),map_one]
  have hq : r (IntegralFormalAddition318.q D)≠0 := by
    intro hh
    rw [hh,mul_zero] at hinv
    exact zero_ne_one hinv
  rw [←er,←rq]
  apply (eq_div_iff hq).mpr
  calc
    r (IntegralFormalAddition318.f D V)*r (IntegralFormalAddition318.q D)=r (IntegralFormalAddition318.n V) := by
      rw [IntegralFormalAddition318.f,map_mul,mul_assoc,hinv,mul_one]
    _ = _ := by rw [IntegralFormalAddition318.n,map_add,map_mul,map_mul,rx,ra,rvx,rva]


theorem evaluated_ordinate (D : Coeff p) (V : PowerSeries (Coeff p))
    (hV : V.map (toPadic p)=GenericFormalDifferential318.branch (toPadic p D))
    (z : Fin 2 → ℤ_[p]) (hz : ∀i,‖z i‖<1) :
    ((PowerSeries.eval₂ (coefficientMap p)
      (MvPowerSeries.eval₂ (coefficientMap p) z (IntegralFormalAddition318.f D V)) V : ℤ_[p]) : ℚ_[p]) =
    (((PowerSeries.eval₂ (coefficientMap p) (z 0) V:ℤ_[p]):ℚ_[p])*
      ((PowerSeries.eval₂ (coefficientMap p) (z 1) V:ℤ_[p]):ℚ_[p])*
      (1-toPadic p D*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)-
      2*toPadic p D*(z 0:ℚ_[p])*(z 1:ℚ_[p])*((z 0:ℚ_[p])^2+(z 1:ℚ_[p])^2)) /
      (1+toPadic p D*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2)^2 := by
  let e := MvPowerSeries.aeval (R:=Coeff p) (point_hasEval p z hz)
  let r : MvPowerSeries (Fin 2) (Coeff p) →+* ℚ_[p] := PadicInt.Coe.ringHom.comp e.toRingHom
  have er (F : MvPowerSeries (Fin 2) (Coeff p)) : r F=
      ((MvPowerSeries.eval₂ (coefficientMap p) z F : ℤ_[p]):ℚ_[p]) := by
    dsimp only [r,RingHom.comp_apply]
    change (e F:ℚ_[p])=_
    dsimp only [e]
    rw [MvPowerSeries.coe_aeval]
    rfl
  have rx : r IntegralFormalAddition318.x=(z 0:ℚ_[p]) := by
    rw [er]; simp only [IntegralFormalAddition318.x,MvPowerSeries.eval₂_X]
  have ra : r IntegralFormalAddition318.a=(z 1:ℚ_[p]) := by
    rw [er]; simp only [IntegralFormalAddition318.a,MvPowerSeries.eval₂_X]
  have rvx : r (IntegralFormalAddition318.v V IntegralFormalAddition318.x)=
      (PowerSeries.eval₂ (coefficientMap p) (z 0) V : ℤ_[p]) := by
    rw [er,IntegralFormalAddition318.v,evaluation_subst p V _ IntegralFormalAddition318.x_zero z hz]
    simp only [IntegralFormalAddition318.x,MvPowerSeries.eval₂_X]
  have rva : r (IntegralFormalAddition318.v V IntegralFormalAddition318.a)=
      (PowerSeries.eval₂ (coefficientMap p) (z 1) V : ℤ_[p]) := by
    rw [er,IntegralFormalAddition318.v,evaluation_subst p V _ IntegralFormalAddition318.a_zero z hz]
    simp only [IntegralFormalAddition318.a,MvPowerSeries.eval₂_X]
  have rq : r (IntegralFormalAddition318.q D)=1+toPadic p D*(z 0:ℚ_[p])^2*(z 1:ℚ_[p])^2 := by
    rw [IntegralFormalAddition318.q,map_add,map_one,map_mul,map_mul,map_pow,map_pow,rx,ra]
    congr 3
    rw [er,MvPowerSeries.eval₂_C]
    rfl
  have hinv : r ((IntegralFormalAddition318.q D).invOfUnit 1)*r (IntegralFormalAddition318.q D)=1 := by
    rw [←map_mul,MvPowerSeries.invOfUnit_mul _ 1 (by simp),map_one]
  have hq : r (IntegralFormalAddition318.q D)≠0 := by
    intro hh
    rw [hh,mul_zero] at hinv
    exact zero_ne_one hinv

  have rc (c : Coeff p) : r (MvPowerSeries.C c)=toPadic p c := by
    rw [er,MvPowerSeries.eval₂_C]
    rfl
  have hform := IntegralFormalAddition318.formal_branch (toPadic p) (toPadic_injective p) D V hV
  have h := congrArg r hform
  rw [map_mul,map_pow] at h
  have hl : r (V.subst (IntegralFormalAddition318.f D V))=
      ((PowerSeries.eval₂ (coefficientMap p)
        (MvPowerSeries.eval₂ (coefficientMap p) z (IntegralFormalAddition318.f D V)) V:ℤ_[p]):ℚ_[p]) := by
    rw [er,evaluation_subst p V _ (IntegralFormalAddition318.f_zero D V) z hz]
  rw [hl] at h
  rw [←rq]
  apply (eq_div_iff (pow_ne_zero 2 hq)).mpr
  rw [h]
  calc
    _ = r (IntegralFormalAddition318.v V IntegralFormalAddition318.x*
      IntegralFormalAddition318.v V IntegralFormalAddition318.a*
      (1-MvPowerSeries.C D*IntegralFormalAddition318.x^2*IntegralFormalAddition318.a^2)-
      2*MvPowerSeries.C D*IntegralFormalAddition318.x*IntegralFormalAddition318.a*
      (IntegralFormalAddition318.x^2+IntegralFormalAddition318.a^2))*
        (r ((IntegralFormalAddition318.q D).invOfUnit 1)*r (IntegralFormalAddition318.q D))^2 := by ring
    _ = _ := by
      rw [hinv,one_pow,mul_one]
      simp only [map_sub,map_mul,map_add,map_one,map_ofNat,map_pow,rx,ra,rvx,rva,rc]

end
end EvaluatedAddition318
#print axioms EvaluatedAddition318.evaluated_addition

#print axioms EvaluatedAddition318.evaluation_zero_small

#print axioms EvaluatedAddition318.evaluated_branch

#print axioms EvaluatedAddition318.evaluated_parameter

#print axioms EvaluatedAddition318.evaluated_ordinate
