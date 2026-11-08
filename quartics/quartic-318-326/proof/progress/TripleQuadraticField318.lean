module
public import KummerTensorField318
public import ThreeRootOrder318
public import InfinityParameters318
public section
noncomputable section
namespace TripleQuadraticField318
set_option maxHeartbeats 900000
open scoped TensorProduct
open QuadraticPresentation318
variable {F:Type*} [Field F] [CharZero F]
@[expose] def Independent (a:Fin 3→F) : Prop :=
  ¬IsSquare (a 0) ∧ ¬QuadraticTower318.spanSquares [a 0] (a 1) ∧
    ¬QuadraticTower318.spanSquares [a 1,a 0] (a 2)
variable (a:Fin 3→F) [h:Fact (Independent a)]
abbrev L1:=QuadraticAlgebra F (a 0) 0
abbrev L2:=QuadraticAlgebra (L1 a) (algebraMap F (L1 a) (a 1)) 0
abbrev L3:=QuadraticAlgebra (L2 a) (algebraMap F (L2 a) (a 2)) 0
abbrev Raw:=ThreeRootOrder318.Order a
instance field1 : Field (L1 a) := by
  letI:Fact (¬IsSquare (a 0)):=⟨h.out.1⟩
  exact inferInstance
private theorem all_ne_zero (i:Fin 3) : a i≠0 := by
  intro hz
  fin_cases i
  · exact h.out.1 (⟨0,by simpa using hz⟩)
  · exact h.out.2.1 (Or.inl (⟨0,by simpa using hz⟩))
  · exact h.out.2.2 (Or.inl (Or.inl (⟨0,by simpa using hz⟩)))

theorem square1 (x:F) : IsSquare (algebraMap F (L1 a) x) ↔
    QuadraticTower318.spanSquares [a 0] x :=
  SquareReflection318.quadratic_square_iff _ _ (all_ne_zero a 0)
instance field2 : Field (L2 a) := by
  letI:Fact (¬IsSquare (algebraMap F (L1 a) (a 1))):=⟨fun hx=>h.out.2.1 ((square1 a _).mp hx)⟩
  exact inferInstance

theorem square2 (x:F) : IsSquare (algebraMap F (L2 a) x) ↔
    QuadraticTower318.spanSquares [a 1,a 0] x := by
  change IsSquare (algebraMap (L1 a) (L2 a) (algebraMap F (L1 a) x)) ↔ _
  rw [SquareReflection318.quadratic_square_iff _ _
    (by simpa only [map_zero] using (algebraMap F (L1 a)).injective.ne (all_ne_zero a 1))]
  rw [←map_mul,square1,square1]
  rfl
instance field3 : Field (L3 a) := by
  letI:Fact (¬IsSquare (algebraMap F (L2 a) (a 2))):=⟨fun hx=>h.out.2.2 ((square2 a _).mp hx)⟩
  exact inferInstance

theorem degree_eight : Module.finrank F (L3 a)=8 := by
  have h1:Module.finrank F (L1 a)=2:=QuadraticAlgebra.finrank_eq_two _ _
  have h2:Module.finrank F (L2 a)=4 := by
    rw [←Module.finrank_mul_finrank F (L1 a) (L2 a),h1,QuadraticAlgebra.finrank_eq_two]
  rw [←Module.finrank_mul_finrank F (L2 a) (L3 a),h2,QuadraticAlgebra.finrank_eq_two]

@[expose] def pairEquiv : RootRing (a 0)⊗[F]RootRing (a 1)≃ₐ[F]L2 a :=
  (Algebra.TensorProduct.congr (presentationEquiv (a 0)).symm
    (AlgEquiv.refl : RootRing (a 1)≃ₐ[F]RootRing (a 1))).trans
      (KummerTensorField318.baseQuadratic (L1 a) (a 1))
@[expose] def rawEquiv : Raw a≃ₐ[F]L3 a :=
  (Algebra.TensorProduct.assoc F F F (RootRing (a 0)) (RootRing (a 1)) (RootRing (a 2))).symm.trans
    ((Algebra.TensorProduct.congr (pairEquiv a)
      (AlgEquiv.refl : RootRing (a 2)≃ₐ[F]RootRing (a 2))).trans
        (KummerTensorField318.baseQuadratic (L2 a) (a 2)))
theorem actual_field : IsField (Raw a) := (rawEquiv a).toRingEquiv.isField (Field.toIsField _)
theorem actual_degree : Module.finrank F (Raw a)=8 := by
  rw [(rawEquiv a).toLinearEquiv.finrank_eq]
  exact degree_eight a

omit h in
theorem independent_of_products (h:∀s:Finset (Fin 3),s.Nonempty→¬IsSquare (∏i∈s,a i)) :
    Independent a := by
  have h0:¬IsSquare (a 0):=by simpa using h {0} (by simp)
  have h1:¬IsSquare (a 1):=by simpa using h {1} (by simp)
  have h2:¬IsSquare (a 2):=by simpa using h {2} (by simp)
  have h01:¬IsSquare (a 0*a 1):=by simpa [Finset.prod_insert,mul_assoc] using h {0,1} (by simp)
  have h02:¬IsSquare (a 0*a 2):=by simpa [Finset.prod_insert,mul_assoc] using h {0,2} (by simp)
  have h12:¬IsSquare (a 1*a 2):=by simpa [Finset.prod_insert,mul_assoc] using h {1,2} (by simp)
  have h012:¬IsSquare (a 0*a 1*a 2):=by simpa [Finset.prod_insert,mul_assoc] using h {0,1,2} (by simp)
  simp only [Independent,QuadraticTower318.spanSquares,not_or]
  simp only [mul_assoc] at *
  tauto

instance infinityIndependent (c:Fin 4→ℚˣ) : Fact (Independent (InfinityParameters318.parameter c)) :=
  ⟨independent_of_products _ (InfinityParameters318.product_nonsquare c)⟩
theorem infinity_field (c:Fin 4→ℚˣ) : IsField (Raw (InfinityParameters318.parameter c)) := actual_field _
theorem infinity_degree (c:Fin 4→ℚˣ) :
    Module.finrank (RatFunc ℚ) (Raw (InfinityParameters318.parameter c))=8 := actual_degree _
end TripleQuadraticField318
