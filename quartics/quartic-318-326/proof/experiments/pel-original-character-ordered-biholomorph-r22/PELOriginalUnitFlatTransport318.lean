module
public import PELOriginalComplexifiedOrder318
public import QuaternionicUnitPeriodTransport318
public section
noncomputable section
namespace PELOriginalUnitFlatTransport318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalSymplecticCoordinates318 PELOriginalFlatPeriodKernel318
open PELOriginalComplexifiedOrder318 QuaternionicUnitPeriodTransport318

@[expose] def unitMatrixC (u : orderˣ) : Mat := fun i j => (unitMatrix representation order u i j:ℂ)
lemma unitMatrixC_mul_inv (u : orderˣ) : unitMatrixC u*unitMatrixC u⁻¹=1 := by
  have h := unitMatrix_mul_inv representation order u
  ext i j
  have he := congrArg (fun M => (M i j:ℂ)) h
  simpa [unitMatrixC,Matrix.mul_apply,Fin.sum_univ_two] using he
lemma unitMatrixC_inv_mul (u : orderˣ) : unitMatrixC u⁻¹*unitMatrixC u=1 := by
  have h := unitMatrix_inv_mul representation order u
  ext i j
  have he := congrArg (fun M => (M i j:ℂ)) h
  simpa [unitMatrixC,Matrix.mul_apply,Fin.sum_univ_two] using he
@[expose] def rightEquiv (u : orderˣ) : Mat ≃ₗ[ℂ] Mat where
  toFun M := M*unitMatrixC u
  invFun M := M*unitMatrixC u⁻¹
  left_inv := by intro M;rw [Matrix.mul_assoc,unitMatrixC_mul_inv,Matrix.mul_one]
  right_inv := by intro M;rw [Matrix.mul_assoc,unitMatrixC_inv_mul,Matrix.mul_one]
  map_add' := by intro M N;exact Matrix.add_mul _ _ _
  map_smul' := by intro a M;exact Matrix.smul_mul _ _ _

/-- Constant complex-linear automorphism induced by actual RIGHT
multiplication by an original order unit. It is not the left PEL action. -/
@[expose] def transport (u : orderˣ) : Ambient ≃ₗ[ℂ] Ambient :=
  splitEquiv.trans ((rightEquiv u).trans splitEquiv.symm)
lemma split_transport (u : orderˣ) (p : Ambient) :
    split (transport u p)=split p*unitMatrixC u :=
  split_unsplit _
lemma transport_inv (u : orderˣ) (p : Ambient) : transport u⁻¹ (transport u p)=p := by
  apply splitEquiv.injective
  change split (transport u⁻¹ (transport u p))=split p
  rw [split_transport,split_transport,Matrix.mul_assoc,unitMatrixC_mul_inv,Matrix.mul_one]
lemma transport_mul (u v : orderˣ) (p : Ambient) :
    transport v (transport u p)=transport (u*v) p := by
  have hm : unitMatrixC (u*v)=unitMatrixC u*unitMatrixC v := by
    ext i j
    simp [unitMatrixC,unitMatrix,map_mul,Matrix.mul_apply,Fin.sum_univ_two]
  apply splitEquiv.injective
  change split (transport v (transport u p))=split (transport (u*v) p)
  rw [split_transport,split_transport,split_transport,hm,Matrix.mul_assoc]

@[expose] def integralAction (u : orderˣ) (p : Pair) : Pair :=
  coordinates (coordinatesEquiv.symm (coordinatesEquiv (fromPair p)*(u:order)))
lemma integralAction_embed (u : orderˣ) (p : Pair) :
    embed (fromPair (integralAction u p))=embed (fromPair p)*((u:order):PELQuaternionAlgebra318.B) := by
  change embed (fromPair (toPair _))=_
  rw [from_to]
  have h := congrArg (fun x : order => (x:PELQuaternionAlgebra318.B))
    (coordinatesEquiv.apply_symm_apply (coordinatesEquiv (fromPair p)*(u:order)))
  exact h

/-- Exact action on EVERY original integral period, not merely its real
span or a lattice of equal covolume. -/
lemma transport_integral (u : orderˣ) (p : Pair) :
    transport u (integralVector p)=integralVector (integralAction u p) := by
  apply splitEquiv.injective
  change split (transport u (integralVector p))=split (integralVector (integralAction u p))
  rw [split_transport,split_integral,split_integral,integralAction_embed,map_mul]
  ext i j
  simp [unitMatrixC,unitMatrix,Matrix.mul_apply,Fin.sum_univ_two]

/-- Both inclusions of the full original integral lattice follow from the
same unit and its genuine inverse. -/
theorem full_integral_lattice (u : orderˣ) :
    Set.range (fun p => transport u (integralVector p))=Set.range integralVector := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨integralAction u p,(transport_integral u p).symm⟩
  · rintro ⟨p,rfl⟩
    refine ⟨integralAction u⁻¹ p,?_⟩
    rw [←transport_integral u⁻¹ p]
    simpa using transport_inv u⁻¹ (integralVector p)
end PELOriginalUnitFlatTransport318
