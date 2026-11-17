module
public import ActualOriginalCompleteCharacter318
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public section
noncomputable section
namespace ActualOriginalCompleteGaussProduct318
open QuadricCRTAssembly318 ActualOriginalCompleteCharacter318 ActualOriginalRationalPoisson318
open ActualOriginalQuadraticGauss318
open scoped BigOperators
set_option maxHeartbeats 16000000

lemma actual_original_character_product (κ : ℤ) (q : ℕ) [NeZero q]
    (a : ℤ) (m : Coordinates ℤ) (r : Coordinates (ZMod q)) :
    ZMod.stdAddChar ((a : ZMod q)*equation (κ : ZMod q) r+linearResidue q m r) =
      (ZMod.stdAddChar ((a : ZMod q)*r.1.1^2+(m.1.1 : ZMod q)*r.1.1) *
        ZMod.stdAddChar ((a : ZMod q)*r.1.2^2+(m.1.2 : ZMod q)*r.1.2)) *
      ((ZMod.stdAddChar (-(a : ZMod q)*r.2.1.1^2+(m.2.1.1 : ZMod q)*r.2.1.1) *
        ZMod.stdAddChar (-(a : ZMod q)*r.2.1.2^2+(m.2.1.2 : ZMod q)*r.2.1.2)) *
        ZMod.stdAddChar ((-(κ : ZMod q)*(a : ZMod q))*r.2.2^2+(m.2.2 : ZMod q)*r.2.2)) := by
  simp only [←AddChar.map_add_eq_mul]
  congr 1
  simp only [equation,linearResidue]
  ring

/-- Exact product of five literal Gauss sums for the SAME complete
coefficient produced by original rational-arc Poisson. The two positive,
two negative and one -kappa diagonal entries retain their full frequencies. -/
theorem actual_complete_arc_gauss_product (κ : ℤ) (q : ℕ) [NeZero q]
    (a : ℤ) (m : Coordinates ℤ) :
    completeArcCoefficient κ q a m =
      (quadraticGauss q (a : ZMod q) (m.1.1 : ZMod q) *
        quadraticGauss q (a : ZMod q) (m.1.2 : ZMod q)) *
      ((quadraticGauss q (-(a : ZMod q)) (m.2.1.1 : ZMod q) *
        quadraticGauss q (-(a : ZMod q)) (m.2.1.2 : ZMod q)) *
        quadraticGauss q (-(κ : ZMod q)*(a : ZMod q)) (m.2.2 : ZMod q)) := by
  classical
  have hp {A B : Type} [Fintype A] [Fintype B] (f : A → ℂ) (g : B → ℂ) :
      (∑ x : A×B, f x.1*g x.2) = (∑ x : A, f x)*(∑ y : B, g y) := by
    rw [Fintype.sum_prod_type]
    exact (Fintype.sum_mul_sum f g).symm
  rw [actual_complete_arc_modular]
  simp_rw [actual_original_character_product]
  rw [hp,hp,hp,hp]
  rfl

end ActualOriginalCompleteGaussProduct318
