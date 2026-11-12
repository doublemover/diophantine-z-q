module
public import Mathlib.Data.Nat.Basic
public section
-- Intentionally non-admitted negative controls. An error is evidence,
-- not a production theorem or an accepted packet. No explicit placeholder.
namespace BinderExpectedFailure318
namespace DirectProofOnly
variable (p:Prop) (hp:p)
theorem proof:p:=by
  exact hp
end DirectProofOnly
namespace ExplicitOmit
variable (p:Prop) (hp:p)
include hp
omit hp in
theorem proof:p:=by
  exact hp
end ExplicitOmit
end BinderExpectedFailure318
