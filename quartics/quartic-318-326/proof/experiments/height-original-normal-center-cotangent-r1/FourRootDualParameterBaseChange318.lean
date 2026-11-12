module
public import FourRootDualScalarExtension318
public import FourRootDualOverlapTensor318
public section
noncomputable section
namespace FourRootDualParameterBaseChange318
open FourRootIntegralDuality318 FiniteDualTransport318
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (p : Fin 4 → R) (q : Fin 4 → S) (h : ∀ i,algebraMap R S (p i)=q i)
local notation "A" => FourRootOrder318.Order p
local notation "B" => FourRootOrder318.Order (fun i => algebraMap R S (p i))
local notation "C" => FourRootOrder318.Order q

/-- Actual marked-root reparameterization by literal coefficient equality. -/
@[expose] def parameterEquiv : B ≃ₐ[S] C :=
  FourRootUnitScale318.four q (fun i => algebraMap R S (p i)) 1
    (by intro i; simpa using h i)

/-- Genuine balanced scalar extension, followed by the actual whole dual
transport across the coefficient equality. This retains the full source map. -/
@[expose] def squareMap :=
  (squareTransport (parameterEquiv p q h)).comp
    (FourRootDualScalarExtension318.squareMap (S:=S) p)

lemma squareMap_frame (x : A) : squareMap p q h (squareFrame (frame p) x)=
    squareFrame (frame q)
      (parameterEquiv p q h (FourRootSignBaseChange318.coefficientMap p S x)) := by
  change squareTransport (parameterEquiv p q h)
    (FourRootDualScalarExtension318.squareMap (S:=S) p (squareFrame (frame p) x))=_
  rw [FourRootDualScalarExtension318.squareMap_frame]
  rw [parameterEquiv,FourRootDualOverlapTensor318.tensor_generator]
  simp only [Units.inv_one,Units.val_one,one_pow,map_one,mul_one]

lemma squareMap_scalar (x : R) : squareMap p q h
    (squareFrame (frame p) (algebraMap R A x))=
      squareFrame (frame q) (algebraMap S C (algebraMap R S x)) := by
  rw [squareMap_frame,AlgHom.commutes,IsScalarTower.algebraMap_apply R S B,AlgEquiv.commutes]
end FourRootDualParameterBaseChange318
