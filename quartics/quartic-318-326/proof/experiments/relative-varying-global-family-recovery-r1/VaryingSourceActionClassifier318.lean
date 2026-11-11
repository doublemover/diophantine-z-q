module
public import VaryingSourceActionParameter318
public section
noncomputable section
namespace VaryingSourceActionClassifier318
open VaryingCommutingMatrixRing318 VaryingSourceActionEquations318
open VaryingSourceActionParameter318
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]

/-- These are actual algebra homomorphisms from the original source,
not assignments of commuting generators with relations left unproved. -/
structure Action where
  map : A →ₐ[R] Matrix ι ι S
  marked : ι → S

@[expose] def action (d : Point R A ι S) : Action R A ι S where
  map :=
    { toFun := d.val.matrices
      map_zero' := by ext i j; exact d.property (.zero i j)
      map_one' := by ext i j; exact sub_eq_zero.mp (d.property (.one i j))
      map_add' := by intro a b; ext i j; exact sub_eq_zero.mp (d.property (.add a b i j))
      map_mul' := by intro a b; ext i j; exact sub_eq_zero.mp (d.property (.mul a b i j))
      commutes' := by intro r; ext i j; exact sub_eq_zero.mp (d.property (.scalar r i j)) }
  marked := d.val.marked

@[expose] def point (a : Action R A ι S) : Point R A ι S :=
  ⟨{matrices := a.map,marked := a.marked,commute := fun x y => by
      rw [← map_mul,← map_mul,mul_comm x y]},by
    intro t
    cases t <;> simp [equation]⟩

@[expose] def actionPoints : Point R A ι S ≃ Action R A ι S where
  toFun := action R A ι S
  invFun := point R A ι S
  left_inv d := by apply Subtype.ext; apply Data.ext <;> rfl
  right_inv a := by cases a; rfl

/-- A two-sided all-ring classifier for framed original-source actions
and one marked vector. This is not yet the cyclic quotient classifier. -/
@[expose] def classifier : (ring R A ι →ₐ[R] S) ≃ Action R A ι S :=
  (pointsWithRelations R A ι S).trans (actionPoints R A ι S)
end VaryingSourceActionClassifier318
