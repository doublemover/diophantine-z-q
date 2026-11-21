module
public import SelectedGeneralizedGeometricJetAxes318
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SelectedGeneralizedGluedCarrier318 SelectedGeneralizedGeometricIdentityJets318
open SelectedGeneralizedGeometricJetAxes318

namespace SelectedGeneralizedGeometricMulJet318

universe u
variable {R : Type u} [CommRing R] {d : Rˣ}

/-- The repeated addition is constructed on the same actual scheme
points. No separate multiplication map or differential is supplied. -/
@[expose] def iterate (A : ActualAddition d) {X : Scheme} {b : X ⟶ Base R}
    (p : Points d b) : ℕ → Points d b
  | 0 => zeroPoint d b
  | m+1 => sum A (iterate A p m) p

/-- Natural multiplication morphism, defined by applying the already
constructed natural iteration to the identity point. -/
@[expose] def multiply (A : ActualAddition d) (m : ℕ) : Carrier d ⟶ Carrier d :=
  (iterate A (identityPoint d) m).val

theorem multiply_over (A : ActualAddition d) (m : ℕ) :
    multiply A m ≫ overBase d = overBase d :=
  (iterate A (identityPoint d) m).property

theorem multiply_test (A : ActualAddition d) {X : Scheme} {b : X ⟶ Base R}
    (p : Points d b) (m : ℕ) :
    p.val ≫ multiply A m = (iterate A p m).val := by
  induction m with
  | zero =>
    change p.val ≫ (overBase d ≫ identitySection d) = b ≫ identitySection d
    rw [← Category.assoc,p.property]
  | succ m ih =>
    change p.val ≫ (sum A (iterate A (identityPoint d) m) (identityPoint d)).val =
      (sum A (iterate A p m) p).val
    exact sum_pull_val A p.val (iterate A (identityPoint d) m) (identityPoint d)
      (iterate A p m) p ih (Category.comp_id _)

variable {V : Type u} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

theorem iterate_jet (A : ActualAddition d) (v : V) (m : ℕ) :
    iterate A (jetPoint d v) m = jetPoint d (m • v) := by
  induction m with
  | zero =>
    change zeroPoint d (jetBase R V) = jetPoint d (0 • v)
    rw [zero_nsmul,jet_zero]
  | succ m ih =>
    change sum A (iterate A (jetPoint d v) m) (jetPoint d v) =
      jetPoint d ((m+1) • v)
    rw [ih,add_nsmul,one_nsmul,jet_sum A]

/-- The literal generalized multiplication map acts on all square-zero
identity vectors by m, including when the residue characteristic
divides m. The only geometric input here is its true addition and
unit axes on the fixed glued carrier. -/
theorem multiply_jet (A : ActualAddition d) (v : V) (m : ℕ) :
    geomJet d v ≫ multiply A m = geomJet d (m • v) :=
  (multiply_test A (jetPoint d v) m).trans (congrArg Subtype.val (iterate_jet A v m))

theorem geomJet_zero_map (d : Rˣ) :
    geomJet d (0:V) = jetBase R V ≫ identitySection d :=
  congrArg Subtype.val (jet_zero d (V := V))

/-- Actual test factor through the scheme-theoretic kernel uses m·v=0,
not equality on geometric/reduced points. -/
theorem jet_killed_iff (A : ActualAddition d) (v : V) (m : ℕ) :
    geomJet d v ≫ multiply A m = jetBase R V ≫ identitySection d ↔ m • v = 0 := by
  rw [multiply_jet,← geomJet_zero_map d]
  exact ⟨geomJet_injective d,congrArg (geomJet d)⟩

end SelectedGeneralizedGeometricMulJet318

#print axioms SelectedGeneralizedGeometricMulJet318.multiply_jet
#print axioms SelectedGeneralizedGeometricMulJet318.jet_killed_iff
