module
public import Mathlib.Data.Nat.Basic
public section
set_option pp.explicit true
set_option pp.universes true
-- HOSTED322 rejects the instance declaration itself: hp is uninferable.
-- Any subsequent printed proof type is in a failed file, not accepted evidence.
namespace BinderLocalInstanceExpectedFailure318
namespace LocalInstance
variable (p:Prop) (hp:p)
local instance suppliedFact:Fact p:=⟨hp⟩
theorem proof:p:=Fact.out
#check @proof
end LocalInstance
end BinderLocalInstanceExpectedFailure318
