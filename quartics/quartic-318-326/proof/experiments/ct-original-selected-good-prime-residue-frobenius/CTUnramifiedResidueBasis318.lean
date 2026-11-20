module
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Unramified.LocalRing
public section
noncomputable section

namespace CTUnramifiedResidueBasis318

open TensorProduct
open IsLocalRing
open scoped TensorProduct

section Quotient

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Reduce a supplied integral basis by literal tensor base change.
The target quotient is by the extended ideal, not an unrelated field. -/
def quotBasis (I : Ideal R) (b : Basis ι R S) :
    Basis ι (R ⧸ I) (S ⧸ I.map (algebraMap R S)) :=
  (b.baseChange (R ⧸ I)).map
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv

theorem quotBasis_apply (I : Ideal R) (b : Basis ι R S) (j : ι) :
    quotBasis I b j = Ideal.Quotient.mk (I.map (algebraMap R S)) (b j) := by
  rw [quotBasis,Module.Basis.map_apply,Module.Basis.baseChange_apply]
  change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm (1 ⊗ₜ[R] b j) = _
  rw [← Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,AlgEquiv.symm_apply_apply]

theorem quotBasis_repr_mk (I : Ideal R) (b : Basis ι R S) (x : S) (i : ι) :
    (quotBasis I b).repr (Ideal.Quotient.mk (I.map (algebraMap R S)) x) i =
      Ideal.Quotient.mk I (b.repr x i) := by
  change (b.baseChange (R ⧸ I)).repr
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
      (Ideal.Quotient.mk (I.map (algebraMap R S)) x)) i = _
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,Module.Basis.baseChange_repr_tmul,
    Algebra.smul_def,mul_one] <;> rfl

end Quotient

section LiteralResidue

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- The equality of maximal ideal with the extension of the base
ideal identifies the actual local residue field, with the actual
residue scalar structure. -/
def toActualResidue
    (hI : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    (S ⧸ (maximalIdeal R).map (algebraMap R S)) ≃ₐ[ResidueField R] ResidueField S where
  __ := Ideal.quotEquivOfEq hI
  commutes' := by
    intro a
    obtain ⟨r,rfl⟩ := (residue_surjective (R := R)) a
    change Ideal.quotEquivOfEq hI
      (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) (algebraMap R S r)) =
        residue S (algebraMap R S r)
    exact Ideal.quotEquivOfEq_mk hI _

theorem toActualResidue_mk
    (hI : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) (x : S) :
    toActualResidue hI (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) x) =
      residue S x :=
  Ideal.quotEquivOfEq_mk hI _

/-- The SAME supplied integral basis reduced to the actual residue
extension. No independent choice of a basis or residue isomorphism. -/
def residueBasis
    (hI : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) (b : Basis ι R S) :
    Basis ι (ResidueField R) (ResidueField S) :=
  (quotBasis (maximalIdeal R) b).map (toActualResidue hI).toLinearEquiv

theorem residueBasis_apply
    (hI : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (b : Basis ι R S) (i : ι) :
    residueBasis hI b i = residue S (b i) := by
  rw [residueBasis,Module.Basis.map_apply,quotBasis_apply]
  exact toActualResidue_mk hI (b i)

theorem residueBasis_repr
    (hI : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S)
    (b : Basis ι R S) (x : S) (i : ι) :
    (residueBasis hI b).repr (residue S x) i = residue R (b.repr x i) := by
  rw [← toActualResidue_mk hI x]
  change (quotBasis (maximalIdeal R) b).repr
    ((toActualResidue hI).symm
      (toActualResidue hI (Ideal.Quotient.mk ((maximalIdeal R).map (algebraMap R S)) x))) i = _
  rw [AlgEquiv.symm_apply_apply]
  exact quotBasis_repr_mk (maximalIdeal R) b x i

/-- An unramified finite local algebra supplies the exact equality
used above, without a second p-adic basis or Nakayama step. -/
theorem maximalIdeal_map_of_unramified [EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    (maximalIdeal R).map (algebraMap R S) = maximalIdeal S :=
  Algebra.FormallyUnramified.map_maximalIdeal

end LiteralResidue
end CTUnramifiedResidueBasis318
