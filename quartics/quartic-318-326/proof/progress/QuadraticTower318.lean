module
public import SquareReflection318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace QuadraticTower318
set_option maxHeartbeats 900000
variable {F:Type*} [Field F] [CharZero F]
@[expose] def spanSquares : List F→F→Prop
  | [],x=>IsSquare x
  | a::l,x=>spanSquares l x ∨ spanSquares l (a*x)
@[expose] def Independent (a:Fin 4→F) : Prop :=
  ¬IsSquare (a 0) ∧ ¬spanSquares [a 0] (a 1) ∧
    ¬spanSquares [a 1,a 0] (a 2) ∧ ¬spanSquares [a 2,a 1,a 0] (a 3)
variable (a:Fin 4→F) [h:Fact (Independent a)]
abbrev L1:=QuadraticAlgebra F (a 0) 0
abbrev L2:=QuadraticAlgebra (L1 a) (algebraMap F (L1 a) (a 1)) 0
abbrev L3:=QuadraticAlgebra (L2 a) (algebraMap F (L2 a) (a 2)) 0
abbrev L4:=QuadraticAlgebra (L3 a) (algebraMap F (L3 a) (a 3)) 0

instance field1 : Field (L1 a) := by
  letI:Fact (¬IsSquare (a 0)):=⟨h.out.1⟩
  exact inferInstance

private theorem all_ne_zero (i:Fin 4) : a i≠0 := by
  intro hz
  fin_cases i
  · exact h.out.1 (⟨0,by simpa using hz⟩)
  · exact h.out.2.1 (Or.inl (⟨0,by simpa using hz⟩))
  · exact h.out.2.2.1 (Or.inl (Or.inl (⟨0,by simpa using hz⟩)))
  · exact h.out.2.2.2 (Or.inl (Or.inl (Or.inl (⟨0,by simpa using hz⟩))))

theorem square1 (x:F) : IsSquare (algebraMap F (L1 a) x) ↔ spanSquares [a 0] x :=
  SquareReflection318.quadratic_square_iff _ _ (all_ne_zero a 0)

instance field2 : Field (L2 a) := by
  letI:Fact (¬IsSquare (algebraMap F (L1 a) (a 1))):=⟨fun hx=>h.out.2.1 ((square1 a _).mp hx)⟩
  exact inferInstance

theorem square2 (x:F) : IsSquare (algebraMap F (L2 a) x) ↔ spanSquares [a 1,a 0] x := by
  change IsSquare (algebraMap (L1 a) (L2 a) (algebraMap F (L1 a) x)) ↔ _
  rw [SquareReflection318.quadratic_square_iff _ _
    (by simpa only [map_zero] using (algebraMap F (L1 a)).injective.ne (all_ne_zero a 1))]
  rw [←map_mul,square1,square1]
  rfl

instance field3 : Field (L3 a) := by
  letI:Fact (¬IsSquare (algebraMap F (L2 a) (a 2))):=⟨fun hx=>h.out.2.2.1 ((square2 a _).mp hx)⟩
  exact inferInstance

theorem square3 (x:F) : IsSquare (algebraMap F (L3 a) x) ↔ spanSquares [a 2,a 1,a 0] x := by
  change IsSquare (algebraMap (L2 a) (L3 a) (algebraMap F (L2 a) x)) ↔ _
  rw [SquareReflection318.quadratic_square_iff _ _
    (by simpa only [map_zero] using (algebraMap F (L2 a)).injective.ne (all_ne_zero a 2))]
  rw [←map_mul,square2,square2]
  rfl

instance field4 : Field (L4 a) := by
  letI:Fact (¬IsSquare (algebraMap F (L3 a) (a 3))):=⟨fun hx=>h.out.2.2.2 ((square3 a _).mp hx)⟩
  exact inferInstance

/-- The actual iterated quadratic field has degree16, not an assumed Kummer degree. -/
theorem degree_sixteen : Module.finrank F (L4 a)=16 := by
  have h1:Module.finrank F (L1 a)=2:=QuadraticAlgebra.finrank_eq_two _ _
  have h2:Module.finrank F (L2 a)=4 := by
    rw [←Module.finrank_mul_finrank F (L1 a) (L2 a),h1,QuadraticAlgebra.finrank_eq_two]
  have h3:Module.finrank F (L3 a)=8 := by
    rw [←Module.finrank_mul_finrank F (L2 a) (L3 a),h2,QuadraticAlgebra.finrank_eq_two]
  rw [←Module.finrank_mul_finrank F (L3 a) (L4 a),h3,QuadraticAlgebra.finrank_eq_two]

end QuadraticTower318
