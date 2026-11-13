module
public import SelectedEpsilonLift318
public section
noncomputable section
namespace ActualHalfPointLift318
open ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 1000000

/-- The original explicit halving certificate produces an actual equality
in Mathlib's original short-curve group, including its ordinate sign. -/
theorem half_from_square {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (D rho a : F) (hD : D=(3-rho)^2) (hr : rho^2=2) (ha : a^2=1+rho)
    (hR : (E D).Nonsingular (1+rho) (2*rho)) :
    ∃ Q : (E D).Point, Q+Q=Point.some (1+rho) (2*rho) hR := by
  obtain ⟨x,y,m,hy,hc,hm,hx,hy'⟩ := BranchHalving.explicit_half rho a hr ha
    (by norm_num) (by norm_num)
  have hc' : y^2=x^3-D*x := by rw [hD]; exact hc
  have hm' : 2*y*m=3*x^2-D := by rw [hD]; exact hm
  have hn : (E D).Nonsingular x y := by
    rw [nonsingular_iff']
    refine ⟨?_,Or.inr ?_⟩
    · rw [equation_iff]
      simpa only [E,zero_mul,mul_zero,add_zero,neg_mul,sub_eq_add_neg] using hc'
    · simpa only [E,zero_mul,add_zero] using mul_ne_zero (by norm_num : (2:F)≠0) hy
  have hden : y+y≠0 := by simpa only [←two_mul] using mul_ne_zero (by norm_num : (2:F)≠0) hy
  have hneg : y≠(E D).negY x y := by
    simp only [negY,E,zero_mul,sub_zero]
    intro he
    exact hden (by linear_combination he)
  have hslope : (E D).slope x x y y=m := by
    rw [slope_of_Y_ne rfl hneg]
    simp only [E,zero_mul,add_zero,sub_zero,negY,sub_neg_eq_add]
    apply (div_eq_iff hden).mpr
    linear_combination hm'
  have hx' : (E D).addX x x ((E D).slope x x y y)=1+rho := by
    rw [addX,hslope]
    simp only [E,zero_mul,add_zero,sub_zero]
    linear_combination hx
  have hyy : (E D).addY x x y ((E D).slope x x y y)=2*rho := by
    rw [addY,negAddY,negY,hx',hslope]
    simp only [E,zero_mul,sub_zero]
    linear_combination hy'
  refine ⟨Point.some x y hn,?_⟩
  rw [Point.add_self_of_Y_ne hneg]
  simp only [hx',hyy]

variable (p : ℕ) [Fact p.Prime]
local instance : DecidableEq ConcreteG8Domain.K := Classical.decEq _
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- This is the literal original R, after its actual selected embedding.
The finite root data are explicit; no halving of P=2R is substituted. -/
theorem original_half (rho : ℚ_[p]) (hr : rho^2=2) (hp : p≠2)
    (z t : ZMod p) (hz : z^8= -1) (ht : t^4=2) :
    ∃ Q : (E (ConcretePadic318.embedding p rho hr ConcreteG8Domain.D)).Point,
      Q+Q=ShortCurveBaseChange318.pointMap (ConcretePadic318.embedding p rho hr).toRingHom
        ConcreteG8Domain.D GlobalGeneratorPoints318.R := by
  let phi := (ConcretePadic318.embedding p rho hr).toRingHom
  have hx : phi GlobalGeneratorPoints318.xR=1+rho := by
    simp only [phi,GlobalGeneratorPoints318.xR,ConcretePadic318.embedding_pair,Rat.cast_one,one_mul]
  have hy : phi GlobalGeneratorPoints318.yR=2*rho := by
    simp only [phi,GlobalGeneratorPoints318.yR,ConcretePadic318.embedding_pair,Rat.cast_zero,
      Rat.cast_ofNat,zero_add]
  have hR := ShortCurveBaseChange318.nonsingular_map phi ConcreteG8Domain.D _ _
    GlobalGeneratorPoints318.nonsingularR
  rw [hx,hy] at hR
  obtain ⟨a,ha⟩ := SelectedEpsilonLift318.epsilon_square p rho hr hp z t hz ht
  obtain ⟨Q,hQ⟩ := half_from_square (phi ConcreteG8Domain.D) rho a
    (ActualSplitOrbitEntry318.coefficient_eq p rho hr) hr ha hR
  refine ⟨Q,?_⟩
  rw [GlobalGeneratorPoints318.R,ShortCurveBaseChange318.pointMap_some]
  simpa only [hx,hy] using hQ

end ActualHalfPointLift318
