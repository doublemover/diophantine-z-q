module
public import TwoTwistPointRealization318
public section
noncomputable section
namespace ActualTwoDescentPointExtraction318

/-- Actual rational Kummer coordinates for the original curve
Y²=X(X-n)(X+3n), in the retained descent convention (X+3n,X-n).
This records a rational point, NOT an adelic/local solution or Selmer class.
Existence of this rational data is still the global arithmetic obligation. -/
structure KummerPoint (β n : ℚ) where
  x : ℚ
  y : ℚ
  u : ℚ
  v : ℚ
  x_ne : x ≠ 0
  u_ne : u ≠ 0
  v_ne : v ≠ 0
  curve : y^2=x*(x-n)*(x+3*n)
  first : x+3*n=β*u^2
  second : x-n=v^2

end ActualTwoDescentPointExtraction318
