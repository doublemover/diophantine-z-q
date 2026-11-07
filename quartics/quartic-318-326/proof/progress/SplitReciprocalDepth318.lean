module
public import SourceLogDomain318
public import ActualLogIdentification318
public import ValuationAddition318
public section
namespace SplitReciprocalDepth318
open ActualLogHom318 ActualLogIdentification318 ReciprocalDouble318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
noncomputable section
variable (p:ℕ) [Fact p.Prime]
local instance : DecidableEq ℚ_[p] := Classical.decEq _

/-- Actual affine reciprocal-abscissa depth determines both formal subgroup
membership and exact logarithm depth. No ordinate sign or nonzero assumption
is needed. -/
theorem affine_depth (hp:19≤p) (D f y:ℚ_[p]) (hD:Padic.addValuation D=0)
    (r:ℤ) (hr:1≤r) (hf:Padic.addValuation f=((2*r:ℤ):WithTop ℤ))
    (hns:(E D).Nonsingular (1/f) y) :
    ∃(hDn:‖D‖≤1)(hm:Point.some (1/f) y hns∈formalSubgroup p hp D hDn),
      Padic.addValuation (logHom p hp D hDn ⟨Point.some (1/f) y hns,hm⟩)=(r:ℤ) := by
  have hf0:f≠0 := (Padic.addValuation.ne_top_iff).mp (by rw [hf]; exact WithTop.coe_ne_top)
  have hx0:1/f≠0:=one_div_ne_zero hf0
  have hx:Padic.addValuation (1/f)=((-2*r:ℤ):WithTop ℤ) := by
    rw [Padic.addValuation.map_div,Padic.addValuation.map_one,hf]
    norm_cast
    omega
  have hc:y^2=(1/f)^3-D*(1/f) := by
    have he:=hns.1
    rw [equation_iff] at he
    simpa [E,sub_eq_add_neg] using he
  have hy:y≠0 := by
    intro hy
    have he:(1/f)*((1/f)^2-D)=0 := by rw [hy] at hc; linear_combination -hc
    have hd:(1/f)^2=D := sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left hx0)
    have hv:=congrArg Padic.addValuation hd
    rw [Padic.addValuation.map_pow,hx,hD] at hv
    have hbad:2*(-2*r)=0 := by exact_mod_cast hv
    omega
  obtain ⟨b,hb⟩:=WithTop.ne_top_iff_exists.mp ((Padic.addValuation.ne_top_iff).mpr hy)
  have hab:=ValuationAddition318.ordinate_value Padic.addValuation D (1/f) y (-2*r) b hD hx hb.symm hc (by omega)
  have hby:b= -3*r := by omega
  have hz:Padic.addValuation (-(1/f)/y)=(r:ℤ) := by
    rw [Padic.addValuation.map_div,Padic.addValuation.map_neg,hx,←hb,hby]
    norm_cast
    omega
  obtain ⟨hDn,hm⟩:=SourceLogDomain318.affine_mem_of_valuation p hp D (1/f) y hD hy hc hns r hr hx
    (by rw [hz]; exact WithTop.coe_le_coe.mpr hr)
  refine ⟨hDn,hm,?_⟩
  rw [logHom_z_valuation]
  exact hz

end
end SplitReciprocalDepth318
#print axioms SplitReciprocalDepth318.affine_depth
