module
public import Mathlib.Tactic
public section
namespace WildMixedEvenLastPrefix318
variable {K : Type*} [Field K]
theorem shift_eq (f w S V : K) :
    f*(V+S)^2+w*S*(V+S)+S^2 =
      f*V^2+(2*f+w)*S*V+(f+w+1)*S^2 := by ring
theorem side_conic (s R V : K) : ((s*R)*V)*s^2=s^3*R*V := by ring
end WildMixedEvenLastPrefix318
