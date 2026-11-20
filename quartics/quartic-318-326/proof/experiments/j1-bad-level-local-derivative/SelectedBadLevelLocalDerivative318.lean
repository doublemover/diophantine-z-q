module
public import SelectedNormalizedEtaleDJ318
public import SelectedJOneExactMinorLoss318
import all SelectedJOneExactMinorLoss318
public section
noncomputable section
open Polynomial NumberField SelectedNormalizedEtaleDJ318 SelectedJOneExactMinorLoss318
open scoped BigOperators

namespace SelectedBadLevelLocalDerivative318

section Chart
variable {O A : Type*} [CommRing O] [CommRing A] [Algebra O A]

/-- Substitute the actual j-coordinate in each coefficient of P(J,X). -/
abbrev evalJ (j : A) : O[X] →+* A :=
  Polynomial.eval₂RingHom (algebraMap O A) j

def jDerivative (p : (O[X])[X]) (j x : A) : A :=
  p.sum (fun n a => evalJ j a.derivative * x^n)

abbrev xDerivative (p : (O[X])[X]) (j x : A) : A :=
  p.derivative.eval₂ (evalJ j) x

/-- The actual polynomial relation gives the signed differential relation.
No invertibility of either polynomial derivative is assumed. -/
theorem chart_relation (δ : Derivation O A A) (p : (O[X])[X]) (j x : A)
    (hp : p.eval₂ (evalJ j) x = 0) :
    xDerivative p j x * δ x = -(jDerivative p j x * δ j) := by
  have hcoef (q : O[X]) : δ (evalJ j q) = evalJ j q.derivative * δ j := by
    change δ (q.eval₂ (algebraMap O A) j) = q.derivative.eval₂ (algebraMap O A) j * δ j
    rw [derive_eval₂]
    simp only [Polynomial.sum_def,δ.map_algebraMap,zero_mul,Finset.sum_const_zero,add_zero]
  have hsum : p.sum (fun n a => δ (evalJ j a) * x^n) = jDerivative p j x * δ j := by
    unfold jDerivative
    simp only [Polynomial.sum_def,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [hcoef]
    ring
  rw [← hsum]
  exact implicit_relation δ (evalJ j) x p hp

/-- Given the actual local derivative denominator at this section and
a genuine coordinate in the frame, project it to the same coefficient
of dj. The witness is regular even if the j-derivative is not a unit. -/
theorem project_denominator (β : A →ₐ[O] O) (δ : Derivation O A A)
    (p : (O[X])[X]) (j x : A) (hp : p.eval₂ (evalJ j) x = 0)
    (s : Oˣ) (hs : β (δ x) = (s:O)) (a w : O)
    (clears : β (xDerivative p j x) * w = a) :
    ∃ t : O, β (δ j) * t = a := by
  have hrel := congrArg (fun b : A => β b) (chart_relation δ p j x hp)
  simp only [map_mul,map_neg,hs] at hrel
  refine ⟨-β (jDerivative p j x) * (↑s⁻¹:O) * w,?_⟩
  calc
    _ = -(β (jDerivative p j x) * β (δ j)) * (↑s⁻¹:O) * w := by ring
    _ = β (xDerivative p j x) * w := by
      rw [← hrel,mul_assoc (β (xDerivative p j x)) (s:O),Units.mul_inv,mul_one]
    _ = a := clears

/-- The same literal section above j=1, including the sign of the actual
dual numerator M*j*(j-1728). -/
theorem literal_one_denominator (β : A →ₐ[O] O) (δ : Derivation O A A)
    (p : (O[X])[X]) (j x : A) (hp : p.eval₂ (evalJ j) x = 0) (h1 : β j = 1)
    (s : Oˣ) (hs : β (δ x) = (s:O)) (M : ℕ) (w : O)
    (clears : β (xDerivative p j x) * w = β ((M:A)*j*(j-1728))) :
    ∃ t : O, β (δ j) * t = -((1727*M:ℕ):O) := by
  apply project_denominator β δ p j x hp s hs _ w
  rw [clears]
  simp only [map_mul,map_natCast,h1,map_sub,map_ofNat,Nat.cast_mul]
  ring

end Chart

section GenuineFinitePlace
variable {L : Type*} [Field L] [NumberField L] (v : FinitePlace L)
local notation "O" => integralAt v

/-- Keep the actual generic ordered minor and basis change unchanged.
Projection supplies row witnesses, while the determinant loss survives
with its correct sign. No determinant valuation is inferred from
ramification or from the existence of a regular chart alone. -/
theorem one_place_budget {g : ℕ}
    (m C : Matrix (Fin g) (Fin g) L) (hm : m.det ≠ 0) (hC : C.det ≠ 0)
    (u : Fin g → L) (I : Matrix (Fin g) (Fin g) O)
    (frames : baseMatrix v I = Matrix.diagonal u * m * C)
    (a : L) (ha : a ≠ 0)
    (clears : ∀ i, ∃ t : O, u i * algebraMap O L t = a) :
    -Real.log (v ((m.det*C.det)⁻¹)) ≤
      (g:ℝ)*(-Real.log (v a)) - (-Real.log (v (baseMatrix v I).det)) := by
  have hu (i : Fin g) : u i ≠ 0 := by
    obtain ⟨t,ht⟩ := clears i
    intro h
    rw [h,zero_mul] at ht
    exact ha ht.symm
  have hcol (i : Fin g) : -Real.log (v (u i)) ≤ -Real.log (v a) := by
    obtain ⟨t,ht⟩ := clears i
    have ht' : v (algebraMap O L t) ≤ 1 := t.property
    apply neg_le_neg
    apply Real.log_le_log (FinitePlace.pos_iff.mpr ha)
    rw [← ht,map_mul]
    exact mul_le_of_le_one_right (apply_nonneg v _) ht'
  rw [(exact_row v m C hm hC u hu I frames).2]
  apply sub_le_sub_right
  calc
    _ ≤ ∑ _i : Fin g, -Real.log (v a) := Finset.sum_le_sum fun i _ => hcol i
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

end GenuineFinitePlace
end SelectedBadLevelLocalDerivative318

#print axioms SelectedBadLevelLocalDerivative318.chart_relation
#print axioms SelectedBadLevelLocalDerivative318.project_denominator
#print axioms SelectedBadLevelLocalDerivative318.literal_one_denominator
#print axioms SelectedBadLevelLocalDerivative318.one_place_budget
