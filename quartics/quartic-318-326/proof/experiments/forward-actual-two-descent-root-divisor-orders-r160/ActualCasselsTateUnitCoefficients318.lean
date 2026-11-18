module
public import ActualTwoDescentSquareOneBinary318
public import ActualTwoDescentClosureFieldEmbedding318
import all ActualTwoDescentSquareOneBinary318
import all ActualTwoDescentFieldSquareOneUnits318
public section
noncomputable section
namespace ActualCasselsTateUnitCoefficients318

open ActualTwoDescentSquareOneBinary318 ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentClosureFieldEmbedding318
variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L]

/-- The literal inclusion F₂ ≃ μ₂ ↪ Kˣ. The codomain is all field units. -/
def binaryUnit (a : ZMod 2) : Kˣ :=
  (squareOneBinaryEquiv.symm (Multiplicative.ofAdd a) : SquareOne K)

@[simp] lemma binaryUnit_zero : binaryUnit (K:=K) 0=1 :=
  congrArg (fun u : SquareOne K => (u : Kˣ)) (map_one squareOneBinaryEquiv.symm)

lemma binaryUnit_add (a b : ZMod 2) :
    binaryUnit (K:=K) (a+b)=binaryUnit a*binaryUnit b :=
  congrArg (fun u : SquareOne K => (u : Kˣ))
    (squareOneBinaryEquiv.symm.map_mul (Multiplicative.ofAdd a) (Multiplicative.ofAdd b))

lemma binaryUnit_neg (a : ZMod 2) : binaryUnit (K:=K) (-a)=(binaryUnit a)⁻¹ :=
  congrArg (fun u : SquareOne K => (u : Kˣ))
    (map_inv squareOneBinaryEquiv.symm (Multiplicative.ofAdd a))

lemma binaryUnit_sub (a b : ZMod 2) :
    binaryUnit (K:=K) (a-b)=binaryUnit a/binaryUnit b := by
  rw [sub_eq_add_neg,binaryUnit_add,binaryUnit_neg,div_eq_mul_inv]

/-- Coefficient extension preserves the literal signs, not just their bits. -/
lemma binaryUnit_map (f : K →+* L) (a : ZMod 2) :
    Units.map f.toMonoidHom (binaryUnit a)=binaryUnit (K:=L) a := by
  fin_cases a <;> apply Units.ext <;>
    simp [binaryUnit,squareOneBinaryEquiv,binarySquareOne,negativeOne]

variable {F : Type} [Field F] [CharZero F]
local notation "Gal" => Field.absoluteGaloisGroup F
local notation "Qbar" => AlgebraicClosure F

/-- The actual action on ALL algebraic-closure units. It is not made trivial. -/
def unitAction (σ : Gal) : Qbarˣ →* Qbarˣ :=
  Units.map σ.toRingHom.toMonoidHom

lemma unitAction_one (u : Qbarˣ) : unitAction (1 : Gal) u=u := by
  apply Units.ext
  rfl

lemma unitAction_mul (σ τ : Gal) (u : Qbarˣ) :
    unitAction (σ*τ) u=unitAction σ (unitAction τ u) := by
  apply Units.ext
  rfl

/-- Only the sign subgroup is fixed under the actual coefficient action. -/
lemma unitAction_binaryUnit (σ : Gal) (a : ZMod 2) :
    unitAction σ (binaryUnit (K:=Qbar) a)=binaryUnit a := by
  apply Units.ext
  exact actual_square_one_aut_fixed σ
    (squareOneBinaryEquiv.symm (Multiplicative.ofAdd a))

/-- Inhomogeneous multiplicative degree-two differential with actual action. -/
def unitDTwo (c : Gal → Gal → Qbarˣ) (σ τ υ : Gal) : Qbarˣ :=
  unitAction σ (c τ υ)/c (σ*τ) υ*c σ (τ*υ)/c σ τ

/-- Inhomogeneous multiplicative degree-three differential with actual action. -/
def unitDThree (c : Gal → Gal → Gal → Qbarˣ) (σ τ υ ω : Gal) : Qbarˣ :=
  unitAction σ (c τ υ ω)/c (σ*τ) υ ω*c σ (τ*υ) ω/c σ τ (υ*ω)*c σ τ υ

lemma unitDTwo_binary (c : Gal → Gal → ZMod 2) (σ τ υ : Gal) :
    unitDTwo (fun a b => binaryUnit (c a b)) σ τ υ=
      binaryUnit (c τ υ-c (σ*τ) υ+c σ (τ*υ)-c σ τ) := by
  simp only [unitDTwo,unitAction_binaryUnit,binaryUnit_add,binaryUnit_sub]

lemma unitDThree_binary (c : Gal → Gal → Gal → ZMod 2) (σ τ υ ω : Gal) :
    unitDThree (fun a b d => binaryUnit (c a b d)) σ τ υ ω=
      binaryUnit (c τ υ ω-c (σ*τ) υ ω+c σ (τ*υ) ω-c σ τ (υ*ω)+c σ τ υ) := by
  simp only [unitDThree,unitAction_binaryUnit,binaryUnit_add,binaryUnit_sub]

variable {E : Type} [Field E] [CharZero E]

/-- Actual closure-unit coefficient transport for field restriction. -/
def closureUnitMap (f : F →+* E) : Qbarˣ →* (AlgebraicClosure E)ˣ :=
  Units.map (closureMap f).toMonoidHom

lemma closureUnitMap_binary (f : F →+* E) (a : ZMod 2) :
    closureUnitMap f (binaryUnit a)=binaryUnit (K:=AlgebraicClosure E) a :=
  binaryUnit_map (closureMap f) a

/-- Equivariance on arbitrary units, not just roots of unity. -/
lemma closureUnitMap_action (f : F →+* E) (σ : Field.absoluteGaloisGroup E) (u : Qbarˣ) :
    closureUnitMap f (unitAction (Field.absoluteGaloisGroup.map f σ) u)=
      unitAction σ (closureUnitMap f u) := by
  apply Units.ext
  exact actual_closure_map_galois f σ (u : Qbar)

/-- Genuine coefficient restriction commutes with the degree-two differential. -/
lemma unitDTwo_restriction (f : F →+* E) (c : Gal → Gal → Qbarˣ)
    (σ τ υ : Field.absoluteGaloisGroup E) :
    unitDTwo (fun a b => closureUnitMap f
      (c (Field.absoluteGaloisGroup.map f a) (Field.absoluteGaloisGroup.map f b))) σ τ υ=
      closureUnitMap f (unitDTwo c (Field.absoluteGaloisGroup.map f σ)
        (Field.absoluteGaloisGroup.map f τ) (Field.absoluteGaloisGroup.map f υ)) := by
  simp only [unitDTwo,map_div,map_mul,closureUnitMap_action]

end ActualCasselsTateUnitCoefficients318
