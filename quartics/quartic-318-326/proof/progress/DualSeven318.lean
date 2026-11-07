module
public import DualLocalArithmetic318
public import Mathlib.NumberTheory.Padics.RingHoms
public section
namespace DualSeven318
set_option maxHeartbeats 0
local instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem residue_no_root : ∀u:ZMod 7,u^2+4≠0 := by decide +kernel

theorem residue_two_square : ∃ x : ZMod 7, x^2=2 := by
  exact ⟨3,by decide +kernel⟩

/-- The exceptional polynomial has no zero over the actual residue field. -/
theorem integral_square_add_four_unit (u:ℤ_[7]) : IsUnit (u^2+4) := by
  have hres:PadicInt.toZMod (u^2+4)≠0 := by
    simpa only [map_add,map_pow,map_ofNat] using residue_no_root (PadicInt.toZMod u)
  have hnot:u^2+4∉IsLocalRing.maximalIdeal ℤ_[7] := by
    rw [←PadicInt.ker_toZMod]
    exact hres
  simpa only [IsLocalRing.mem_maximalIdeal,mem_nonunits_iff,not_not] using hnot

/-- At the actual normalized7-adic place, a unit u has u²+4 a unit. -/
theorem padic_square_add_four_value (u:ℚ_[7]) (hu:Padic.addValuation u=0) :
    Padic.addValuation (u^2+4)=0 := by
  have hu0:u≠0 := (Padic.addValuation.ne_top_iff).mp (by rw [hu]; simp)
  have huv:u.valuation=0 := by
    have hh := Padic.addValuation.apply hu0
    rw [hu] at hh
    exact_mod_cast hh.symm
  have hun:‖u‖=1 := by rw [Padic.norm_eq_zpow_neg_valuation hu0,huv]; norm_num
  let ui:ℤ_[7] := ⟨u,hun.le⟩
  have hn:‖ui^2+4‖=1 := PadicInt.isUnit_iff.mp (integral_square_add_four_unit ui)
  have ht:((ui^2+4:ℤ_[7]):ℚ_[7])=u^2+4 := rfl
  have hn':‖u^2+4‖=1 := by rw [←ht,PadicInt.norm_coe]; exact hn
  have ht0:u^2+4≠0 := by intro hz; rw [hz,norm_zero] at hn'; norm_num at hn'
  have hv:(u^2+4).valuation=0 := by
    rw [Padic.norm_eq_zpow_neg_valuation ht0] at hn'
    have hh := (zpow_eq_one_iff_right₀ (by norm_num:(0:ℝ)≤7) (by norm_num:(7:ℝ)≠1)).mp hn'
    omega
  rw [Padic.addValuation.apply ht0,hv]
  rfl

open ConcreteG8Domain
open scoped QuadraticAlgebra

/-- The two actual places above7 have delta-values0 and1, in either order. -/
theorem delta_value_zero_or_one (v:AddValuation K (WithTop ℤ))
    (h2:v (2:K)=0) (h3:v (3:K)=0) (h7:v (7:K)=1) :
    v (3-i)=0 ∨ v (3-i)=1 := by
  have hi0:i≠0 := by intro h; have hh:=congrArg QuadraticAlgebra.im h; norm_num [i,pair] at hh
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hi0)
  have hh:=congrArg v i_square
  rw [v.map_pow,←ha,h2] at hh
  have ha0:a=0 := by
    have he:2*a=0 := by exact_mod_cast hh
    omega
  have hi:v i=0 := by simpa [ha0] using ha.symm
  have hprod:(3-i)*(3+i)=(7:K) := by ext <;> norm_num [i,pair]
  have hn:(3-i)*(3+i)≠(0:K) := by rw [hprod]; norm_num
  obtain ⟨b,hb⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr (mul_ne_zero_iff.mp hn).1)
  obtain ⟨c,hc⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr (mul_ne_zero_iff.mp hn).2)
  have hb0:0≤b := by
    have hh:=v.map_le_sub (show 0≤v (3:K) by rw [h3]) (show 0≤v i by rw [hi])
    rw [←hb] at hh; exact_mod_cast hh
  have hc0:0≤c := by
    have hh:=v.map_le_add (show 0≤v (3:K) by rw [h3]) (show 0≤v i by rw [hi])
    rw [←hc] at hh; exact_mod_cast hh
  have hsum:=congrArg v hprod
  rw [v.map_mul,←hb,←hc,h7] at hsum
  have hsum':b+c=1 := by exact_mod_cast hsum
  have hor:b=0 ∨ b=1 := by omega
  rcases hor with rfl|rfl
  · exact Or.inl hb.symm
  · exact Or.inr hb.symm

theorem place_apply (rho:ℚ_[7]) (hr:rho^2=2) (x:K) :
    ConcretePadic318.place 7 rho hr x=
      Padic.addValuation (ConcretePadic318.embedding 7 rho hr x) := by
  obtain ⟨a,b⟩:=x
  change ConcretePadic318.place 7 rho hr (pair a b)=Padic.addValuation (ConcretePadic318.embedding 7 rho hr (pair a b))
  rw [ConcretePadic318.place_pair,ConcretePadic318.embedding_pair]

/-- The exceptional valuation-one case is discharged at every actual
7-adic embedding by the proved F7 residue obstruction. -/
theorem dual_seven_even (rho:ℚ_[7]) (hr:rho^2=2) (X Y:K) (m:ℤ)
    (hX:ConcretePadic318.place 7 rho hr X=m) (he:Y^2=X^3+4*D*X) : Even m := by
  let v:=ConcretePadic318.place 7 rho hr
  have h2:v (2:K)=0 := SourcePadic318.place_nat_unit 7 rho hr 2 (by norm_num)
  have h3:v (3:K)=0 := SourcePadic318.place_nat_unit 7 rho hr 3 (by norm_num)
  have h7:v (7:K)=1 := by
    change ConcretePadic318.place 7 rho hr (pair 7 0)=1
    rw [ConcretePadic318.place_rational,ConcretePadic318.rational_value 7 _ (by norm_num)]
    have hs:padicValRat 7 (7:ℚ)=1 := by
      convert padicValRat.self (p:=7) (by norm_num) using 1
    rw [hs]
    rfl
  rcases delta_value_zero_or_one v h2 h3 h7 with hd|hd
  · apply DualLocalArithmetic318.dual_good_even v X Y m hX h2 _ he
    rw [D,v.map_pow,hd]; norm_num
  have hA:v (4*D)=2 := by
    have hfour:(4:K)=2^2 := by norm_num
    rw [v.map_mul,hfour,D,v.map_pow,v.map_pow,h2,hd]
    norm_num [two_nsmul]
  rcases DualLocalArithmetic318.dual_delta_even_unless_one v X Y (4*D) m hX hA he with hm|hm
  · exact hm
  subst m
  have hd0:3-i≠(0:K) := (v.ne_top_iff).mp (by rw [hd]; simp)
  have hu:v (X/(3-i))=0 := by rw [v.map_div,hX,hd]; norm_num
  have hu':Padic.addValuation (ConcretePadic318.embedding 7 rho hr (X/(3-i)))=0 := by
    rw [←place_apply]; exact hu
  have hunit:v ((X/(3-i))^2+4)=0 := by
    rw [show v=ConcretePadic318.place 7 rho hr from rfl,place_apply]
    simp only [map_add,map_pow,map_ofNat]
    exact padic_square_add_four_value _ hu'
  exact (DualLocalArithmetic318.dual_delta_exception v X Y (3-i) hd0 hd hX hunit he).elim

end DualSeven318
#print axioms DualSeven318.residue_no_root
#print axioms DualSeven318.integral_square_add_four_unit
#print axioms DualSeven318.padic_square_add_four_value

#print axioms DualSeven318.dual_seven_even
