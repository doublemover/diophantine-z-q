module
public import LinearContactSquareclass318
public import QuadraticTower318
public section
noncomputable section
namespace SourceKummerField318
set_option maxHeartbeats 1000000
open Polynomial

/-- Every nonempty squareclass product is enough to construct all four actual
quadratic field structures, without a supplied Kummer extension theorem. -/
theorem independent_of_products {F:Type*} [Field F] [CharZero F] (a:Fin 4→F)
    (h:∀s:Finset (Fin 4),s.Nonempty→¬IsSquare (∏i∈s,a i)) :
    QuadraticTower318.Independent a := by
  have h0:¬IsSquare (a 0) := by
    simpa [Finset.prod_insert,mul_assoc] using h {0} (by simp)
  have h1:¬IsSquare (a 1) := by
    simpa [Finset.prod_insert,mul_assoc] using h {1} (by simp)
  have h2:¬IsSquare (a 2) := by
    simpa [Finset.prod_insert,mul_assoc] using h {2} (by simp)
  have h3:¬IsSquare (a 3) := by
    simpa [Finset.prod_insert,mul_assoc] using h {3} (by simp)
  have h01:¬IsSquare (a 0*a 1) := by
    simpa [Finset.prod_insert,mul_assoc] using h {0,1} (by simp)
  have h02:¬IsSquare (a 0*a 2) := by
    simpa [Finset.prod_insert,mul_assoc] using h {0,2} (by simp)
  have h03:¬IsSquare (a 0*a 3) := by
    simpa [Finset.prod_insert,mul_assoc] using h {0,3} (by simp)
  have h12:¬IsSquare (a 1*a 2) := by
    simpa [Finset.prod_insert,mul_assoc] using h {1,2} (by simp)
  have h13:¬IsSquare (a 1*a 3) := by
    simpa [Finset.prod_insert,mul_assoc] using h {1,3} (by simp)
  have h23:¬IsSquare (a 2*a 3) := by
    simpa [Finset.prod_insert,mul_assoc] using h {2,3} (by simp)
  have h012:¬IsSquare (a 0*a 1*a 2) := by
    simpa [Finset.prod_insert,mul_assoc] using h {0,1,2} (by simp)
  have h013:¬IsSquare (a 0*a 1*a 3) := by
    simpa [Finset.prod_insert,mul_assoc] using h {0,1,3} (by simp)
  have h023:¬IsSquare (a 0*a 2*a 3) := by
    simpa [Finset.prod_insert,mul_assoc] using h {0,2,3} (by simp)
  have h123:¬IsSquare (a 1*a 2*a 3) := by
    simpa [Finset.prod_insert,mul_assoc] using h {1,2,3} (by simp)
  have h0123:¬IsSquare (a 0*a 1*a 2*a 3) := by
    simpa [Finset.prod_insert,mul_assoc] using h {0,1,2,3} (by simp)
  simp only [QuadraticTower318.Independent,QuadraticTower318.spanSquares,not_or]
  simp only [mul_assoc] at *
  tauto

@[expose] def parameter (c:Fin 4→ℚˣ) (i:Fin 4) : RatFunc ℚ :=
  algebraMap ℚ[X] (RatFunc ℚ) (C (c i:ℚ)*(X-C (LinearContactSquareclass318.contacts i)))

/-- Exact squareclass independence for the source four finite contacts, with
arbitrary nonzero constant twists. -/
theorem product_nonsquare (c:Fin 4→ℚˣ) (s:Finset (Fin 4)) (hs:s.Nonempty) :
    ¬IsSquare (∏i∈s,parameter c i) := by
  have hp:(∏i∈s,parameter c i)=algebraMap ℚ[X] (RatFunc ℚ)
      (C (∏i∈s,(c i:ℚ))*∏i∈s,(X-C (LinearContactSquareclass318.contacts i))) := by
    simp only [parameter,←map_prod,Finset.prod_mul_distrib]
  rw [hp]
  apply LinearContactSquareclass318.source_squareclass_independent s hs
  exact Finset.prod_ne_zero_iff.mpr (fun i hi=>(c i).ne_zero)

theorem independent (c:Fin 4→ℚˣ) : QuadraticTower318.Independent (parameter c) :=
  independent_of_products _ (product_nonsquare c)

instance independentFact (c:Fin 4→ℚˣ) : Fact (QuadraticTower318.Independent (parameter c)) :=
  ⟨independent c⟩

theorem source_field (c:Fin 4→ℚˣ) : IsField (QuadraticTower318.L4 (parameter c)) :=
  Field.toIsField _

/-- This is an actual constructed degree16 field over Q(t), not a field-degree
premise or an assertion identifying the PEL curve with a guessed twist. -/
theorem source_degree_sixteen (c:Fin 4→ℚˣ) :
    Module.finrank (RatFunc ℚ) (QuadraticTower318.L4 (parameter c))=16 :=
  QuadraticTower318.degree_sixteen _
end SourceKummerField318
