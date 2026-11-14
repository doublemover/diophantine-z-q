module
public import Mathlib.Tactic
public section
noncomputable section
namespace FourCharacterRootRecombination318
open Matrix

/-- Product of the other THREE actual character coordinates. -/
@[expose] def triple (v:Fin 4→ℂ) : Fin 4→ℂ:=
  ![v 1*v 2*v 3,v 0*v 2*v 3,v 0*v 1*v 3,v 0*v 1*v 2]
@[expose] def product (v:Fin 4→ℂ):ℂ:=v 0*v 1*v 2*v 3
lemma triple_triple (v:Fin 4→ℂ) (i:Fin 4) :
    triple (triple v) i=v i*(product v)^2 := by
  fin_cases i <;> simp [triple,product] <;> ring
lemma product_triple (v:Fin 4→ℂ) : product (triple v)=(product v)^3 := by
  simp [triple,product]
  ring
lemma product_square (v:Fin 4→ℂ) : (product v)^2=product (fun i=>v i^2) := by
  simp [product,mul_pow]
lemma triple_square (v:Fin 4→ℂ) (i:Fin 4) :
    (triple v i)^2=triple (fun j=>v j^2) i := by
  fin_cases i <;> simp [triple,mul_pow]
lemma triple_div (v:Fin 4→ℂ) (d:ℂ) (i:Fin 4) :
    triple (fun j=>v j/d) i=triple v i/d^3 := by
  fin_cases i <;> simp [triple,div_eq_mul_inv,inv_pow] <;> ring

@[expose] def linear (b:Fin 4→ℂ) (t:ℂ) : Fin 4→ℂ:=fun i=>t-b i
@[expose] def denominator (b:Fin 4→ℂ) (t:ℂ):ℂ:=product (linear b t)
@[expose] def cubic (b:Fin 4→ℂ) (t:ℂ) : Fin 4→ℂ:=triple (linear b t)

abbrev CubicTuple (b:Fin 4→ℂ) (t:ℂ):={y:Fin 4→ℂ // ∀i,y i^2=cubic b t i}
abbrev RootTuple (b:Fin 4→ℂ) (t:ℂ):={z:Fin 4→ℂ // ∀i,z i^2=t-b i}
variable (b:Fin 4→ℂ) (t:ℂ)

lemma cubic_tuple_product (y:CubicTuple b t) : (product y.val)^2=denominator b t^3 := by
  rw [product_square]
  have h:(fun i=>y.val i^2)=cubic b t:=funext y.property
  rw [h]
  exact product_triple (linear b t)
lemma root_tuple_product (z:RootTuple b t) : (product z.val)^2=denominator b t := by
  rw [product_square]
  exact congrArg product (funext z.property)

/-- The inverse-inertia transformation on the ACTUAL simultaneous
character coordinates. It is valid only off the full branch polynomial;
no division at a ramified point is claimed. -/
@[expose] def toRoots (hD:denominator b t≠0) (y:CubicTuple b t) : RootTuple b t:=by
  refine ⟨fun i=>triple y.val i/denominator b t,?_⟩
  intro i
  rw [div_pow,div_eq_iff (pow_ne_zero 2 hD),triple_square]
  have h:(fun j=>y.val j^2)=cubic b t:=funext y.property
  rw [h]
  exact triple_triple (linear b t) i
@[expose] def toCubics (z:RootTuple b t) : CubicTuple b t:=by
  refine ⟨triple z.val,?_⟩
  intro i
  rw [triple_square]
  exact congrArg (fun v:Fin 4→ℂ=>triple v i) (funext z.property)
lemma toCubics_toRoots (hD:denominator b t≠0) (y:CubicTuple b t) :
    toCubics b t (toRoots b t hD y)=y := by
  apply Subtype.ext
  funext i
  change triple (fun j=>triple y.val j/denominator b t) i=y.val i
  rw [triple_div,triple_triple,cubic_tuple_product]
  exact mul_div_cancel_right₀ _ (pow_ne_zero 3 hD)
lemma toRoots_toCubics (hD:denominator b t≠0) (z:RootTuple b t) :
    toRoots b t hD (toCubics b t z)=z := by
  apply Subtype.ext
  funext i
  change triple (triple z.val) i/denominator b t=z.val i
  rw [triple_triple,root_tuple_product]
  exact mul_div_cancel_right₀ _ hD

/-- Exact simultaneous four-root/character-cubic equivalence over the
regular common base. All four coordinates live at the SAME t and the
same original branch parameters; no independent point choices remain. -/
@[expose] def equivalence (hD:denominator b t≠0) : CubicTuple b t≃RootTuple b t where
  toFun:=toRoots b t hD
  invFun:=toCubics b t
  left_inv:=toCubics_toRoots b t hD
  right_inv:=toRoots_toCubics b t hD
end FourCharacterRootRecombination318
