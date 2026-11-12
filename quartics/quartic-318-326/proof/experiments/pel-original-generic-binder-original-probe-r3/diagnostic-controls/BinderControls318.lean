module
public import Mathlib.Data.Nat.Basic
public section
set_option pp.explicit true
set_option pp.universes true
namespace BinderControls318
namespace Explicit
theorem proof (p:Prop) (hp:p):p:=hp
#check @proof
end Explicit
namespace AutomaticSignature
variable (x:Nat)
theorem reflexive:x=x:=rfl
#check @reflexive
end AutomaticSignature
namespace Typeclass
variable (p:Prop) [Fact p]
theorem proof:p:=Fact.out
#check @proof
end Typeclass
namespace DependentSignature
variable (p:Prop) (hp:p)
def witness:p:=hp
theorem identity:witness p hp=hp:=rfl
#check @identity
end DependentSignature
namespace Renamed
variable (p:Prop) (original:p)
include original in
theorem proof:p:=by
  have hb:p:=original
  exact hb
#check @proof
end Renamed
namespace Included
variable (p:Prop) (hp:p)
include hp in
theorem proof:p:=hp
#check @proof
end Included
namespace Omitted
variable (p:Prop) (hp:p)
include hp
omit hp in
theorem noPremise:True:=True.intro
#check @noPremise
end Omitted
end BinderControls318
