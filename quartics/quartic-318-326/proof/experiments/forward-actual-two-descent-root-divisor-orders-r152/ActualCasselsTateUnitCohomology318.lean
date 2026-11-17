module
public import ActualCasselsTateUnitDefect318
import all ActualCasselsTateUnitCoefficients318
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public section
noncomputable section
namespace ActualCasselsTateUnitCohomology318

open ActualCasselsTateUnitCoefficients318 ActualCasselsTateUnitDefect318 groupCohomology
variable {F : Type} [Field F] [CharZero F]
local notation "Gal" => Field.absoluteGaloisGroup F
local notation "Qbar" => AlgebraicClosure F

/-- Additive notation for the genuine action on all closure units. -/
def unitActionAdd (σ : Gal) : Additive Qbarˣ →+ Additive Qbarˣ where
  toFun u := Additive.ofMul (unitAction σ u.toMul)
  map_zero' := congrArg Additive.ofMul ((unitAction σ).map_one)
  map_add' u v := congrArg Additive.ofMul ((unitAction σ).map_mul u.toMul v.toMul)

/-- The actual nontrivial representation on algebraic-closure units. -/
def unitRepresentation : Representation ℤ Gal (Additive Qbarˣ) where
  toFun σ := (unitActionAdd σ).toIntLinearMap
  map_one' := by
    ext u
    exact congrArg Additive.ofMul (unitAction_one u.toMul)
  map_mul' σ τ := by
    ext u
    exact congrArg Additive.ofMul (unitAction_mul σ τ u.toMul)

def unitRep : Rep ℤ Gal := Rep.of (unitRepresentation (F:=F))

lemma unitRep_action (σ : Gal) (u : Additive Qbarˣ) :
    (unitRep (F:=F)).ρ σ u=Additive.ofMul (unitAction σ u.toMul) := rfl

/-- Explicit multiplicative closedness produces a cocycle in native H².
This is abstract cohomology; continuity of each cochain is tracked separately. -/
def unitTwoCocycle (c : Gal → Gal → Qbarˣ)
    (hc : ∀ σ τ υ, unitDTwo c σ τ υ=1) : cocycles₂ (unitRep (F:=F)) := by
  refine ⟨fun g => Additive.ofMul (c g.1 g.2),?_⟩
  apply (mem_cocycles₂_iff _).mpr
  intro σ τ υ
  change Additive.ofMul (c (σ*τ) υ*c σ τ)=
    Additive.ofMul (unitAction σ (c τ υ)*c σ (τ*υ))
  apply congrArg Additive.ofMul
  have h : unitAction σ (c τ υ)*c σ (τ*υ)/(c (σ*τ) υ*c σ τ)=1 := by
    calc
      _ = unitDTwo c σ τ υ := by
        dsimp [unitDTwo]
        simp only [div_eq_mul_inv,mul_inv_rev]
        ac_rfl
      _ = 1 := hc σ τ υ
  exact (div_eq_one_iff_eq.mp h).symm

def unitTwoClass (c : Gal → Gal → Qbarˣ)
    (hc : ∀ σ τ υ, unitDTwo c σ τ υ=1) : H2 (unitRep (F:=F)) :=
  H2π (unitRep (F:=F)) (unitTwoCocycle c hc)

/-- Native H² representative of the actual choice ambiguity between two
coordinate primitives. No claim about its vanishing or invariant is made. -/
def localPrimitiveDifferenceCocycle (c d : Gal → Gal → ZMod 2)
    (h : ∀ σ τ υ : Gal,
      c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
      d τ υ-d (σ*τ) υ+d σ (τ*υ)-d σ τ) : cocycles₂ (unitRep (F:=F)) :=
  unitTwoCocycle (fun a b => binaryUnit (c a b)/binaryUnit (d a b))
    (local_primitive_difference_cocycle c d h)

def localPrimitiveDifferenceClass (c d : Gal → Gal → ZMod 2)
    (h : ∀ σ τ υ : Gal,
      c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
      d τ υ-d (σ*τ) υ+d σ (τ*υ)-d σ τ) : H2 (unitRep (F:=F)) :=
  H2π (unitRep (F:=F)) (localPrimitiveDifferenceCocycle c d h)

lemma localPrimitiveDifferenceCocycle_locally_constant (c d : Gal → Gal → ZMod 2)
    (h : ∀ σ τ υ : Gal,
      c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ=
      d τ υ-d (σ*τ) υ+d σ (τ*υ)-d σ τ)
    (hc : IsLocallyConstant (fun g : Gal × Gal => c g.1 g.2))
    (hd : IsLocallyConstant (fun g : Gal × Gal => d g.1 g.2)) :
    IsLocallyConstant (localPrimitiveDifferenceCocycle c d h : Gal × Gal → Additive Qbarˣ) :=
  (local_primitive_difference_locally_constant c d hc hd).comp Additive.ofMul

end ActualCasselsTateUnitCohomology318
