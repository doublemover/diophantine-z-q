module
public import BivariateIntegral318
public section
noncomputable section
namespace FieldBivariateIntegral318
open Polynomial
variable {K:Type*} [Field K]
/-- The previous rational quotient-integrality proof, with its actual
scalar tower retained, applies over the complex branch field as well. -/
theorem quotient_integral (I:Ideal (MvPolynomial (Fin 2) K))
    [Algebra (Polynomial K) (MvPolynomial (Fin 2) K⧸I)]
    [IsScalarTower K (Polynomial K) (MvPolynomial (Fin 2) K⧸I)]
    (h:∀i:Fin 2,IsIntegral (Polynomial K) (Ideal.Quotient.mk I (MvPolynomial.X i))):
    Algebra.IsIntegral (Polynomial K) (MvPolynomial (Fin 2) K⧸I):=by
  constructor
  intro x
  obtain ⟨f,rfl⟩:=Ideal.Quotient.mk_surjective x
  induction f using MvPolynomial.induction_on with
  | C a=>
    change IsIntegral (Polynomial K) (algebraMap K (MvPolynomial (Fin 2) K⧸I) a)
    rw [IsScalarTower.algebraMap_apply K (Polynomial K) (MvPolynomial (Fin 2) K⧸I)]
    exact isIntegral_algebraMap
  | add f g hf hg=>simpa only [map_add] using hf.add hg
  | mul_X f i hf=>simpa only [map_mul] using hf.mul (h i)
end FieldBivariateIntegral318
