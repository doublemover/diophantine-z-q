module
public import SelectedDenominatorFreeSignChart318
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Quotient
public section
noncomputable section
open Polynomial SelectedDenominatorFreeSignChart318
open scoped BigOperators TensorProduct

namespace SelectedSignIdealDescent318
variable {R : Type*} [CommRing R]

section MonicBasis
variable [nr : Nontrivial R] (b f : R)

include nr in
private theorem degree_two : (equation b f).natDegree = 2 := by
  have ht : (C b*X+C (-f) : R[X]).degree < (X^2:R[X]).degree := by
    rw [Polynomial.degree_X_pow]
    apply lt_of_le_of_lt
      (Polynomial.degree_add_le_of_degree_le (Polynomial.degree_C_mul_X_le b)
        (Polynomial.degree_C_le.trans (by norm_num)) :
        (C b*X+C (-f) : R[X]).degree ≤ 1)
    norm_num
  have he : (equation b f).degree = (X^2:R[X]).degree :=
    Polynomial.degree_add_eq_left_of_degree_lt ht
  rw [Polynomial.natDegree_eq_of_degree_eq he,Polynomial.natDegree_X_pow]

/-- Reduce on the actual power basis of this monic quadratic. This is
not a supplied coordinates or trace decomposition. -/
include nr in
theorem linear_representative (z : RootRing b f) :
    ∃ a c : R, z = algebraMap R (RootRing b f) a +
      algebraMap R (RootRing b f) c * ordinate b f := by
  let P := AdjoinRoot.powerBasis' (monic b f)
  have hdim : P.dim = 2 := by
    change (equation b f).natDegree = 2
    exact degree_two b f
  let E : Fin P.dim ≃ Fin 2 := finCongr hdim
  let B := P.basis.reindex E
  have hB (i : Fin 2) : B i = (ordinate b f) ^ (i:ℕ) := by
    change (P.basis.reindex E) i = _
    rw [Module.Basis.reindex_apply,P.basis_eq_pow] <;> rfl
  have h := B.sum_repr z
  rw [Fin.sum_univ_two,hB,hB] at h
  refine ⟨B.repr z 0,B.repr z 1,?_⟩
  simpa only [Fin.val_zero,Fin.val_one,pow_zero,pow_one,Algebra.smul_def,mul_one] using h.symm

end MonicBasis

section Sign
variable (b f : R)
local notation "Q" => RootRing b f
local notation "y" => ordinate b f
local notation "bQ" => algebraMap R Q b

/-- The actual sign on this quotient fixes the x-line and sends the
chosen ordinate to −y−b, including in characteristic two. -/
@[expose] def sign : Q →ₐ[R] Q :=
  AdjoinRoot.liftAlgHom (equation b f) (Algebra.ofId R Q) (-y-bQ) (by
    change (equation b f).eval₂ (algebraMap R Q) (-y-bQ) = 0
    simp only [equation,eval₂_add,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,map_neg]
    calc
      _ = y^2+bQ*y-algebraMap R Q f := by ring
      _ = 0 := sub_eq_zero.mpr (ordinate_equation b f))

@[simp] theorem sign_ordinate : sign b f y = -y-bQ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem sign_involutive : Function.Involutive (sign b f) := by
  intro z
  have h : (sign b f).comp (sign b f) = AlgHom.id R Q := by
    apply AdjoinRoot.algHom_ext
    change sign b f (sign b f y) = y
    simp only [sign_ordinate,map_sub,map_neg,AlgHom.commutes]
    ring
  exact AlgHom.congr_fun h z

theorem ordinate_discriminant_unit (h : IsUnit (discriminant b f)) : IsUnit (2*y+bQ) := by
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [← derivative_ordinate,derivative_square]
  exact h.map (algebraMap R Q)

variable [nr : Nontrivial R]
variable (I : Ideal Q)
local notation "ι" => algebraMap R Q

/-- Exact gain: a stable ideal descends coefficientwise on the actual
basis 1,y. Subtract sign, then cancel δ=2y+b, NOT 2. This proof
works in characteristic two and uses no Reynolds projector. -/
include nr in
theorem extension_contraction (hD : IsUnit (discriminant b f))
    (stable : ∀ z ∈ I, sign b f z ∈ I) :
    (I.comap ι).map ι = I := by
  apply le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl)
  intro z hz
  obtain ⟨a,c,hzrep⟩ := linear_representative b f z
  have hCoefEq : z - sign b f z = (2*y+bQ) * ι c := by
    rw [hzrep]
    simp only [map_add,map_mul,sign_ordinate,AlgHom.commutes]
    ring
  have hCoefMul : (2*y+bQ) * ι c ∈ I :=
    hCoefEq ▸ I.sub_mem hz (stable z hz)
  have hc : ι c ∈ I := by
    obtain ⟨r,hr⟩ := ordinate_discriminant_unit b f hD
    have h := I.mul_mem_left (↑r⁻¹:Q) hCoefMul
    rwa [← hr,← mul_assoc,Units.inv_mul,one_mul] at h
  have ha : ι a ∈ I := by
    have h := I.sub_mem hz (I.mul_mem_right y hc)
    rw [hzrep, add_sub_cancel_right] at h
    exact h
  have ha' := Ideal.mem_map_of_mem ι (show a ∈ I.comap ι from ha)
  have hc' := Ideal.mem_map_of_mem ι (show c ∈ I.comap ι from hc)
  exact hzrep.symm ▸ ((I.comap ι).map ι).add_mem ha'
    (((I.comap ι).map ι).mul_mem_right y hc')

end Sign

section DescendedOrder
variable (b f : R) (I : Ideal (RootRing b f))
abbrev contraction : Ideal R := I.comap (algebraMap R (RootRing b f))
abbrev SignOrder := R ⧸ contraction b f I
abbrev ClosedOrder :=
  RootRing b f ⧸ (contraction b f I).map (algebraMap R (RootRing b f))

/-- Replacing the ideal of the actual primitive closure by its
extended contraction does not replace the actual closed scheme. -/
theorem closedIdeal_eq [Nontrivial R] (hD : IsUnit (discriminant b f))
    (stable : ∀ z ∈ I, sign b f z ∈ I) :
    (contraction b f I).map (algebraMap R (RootRing b f)) = I :=
  extension_contraction b f I hD stable

theorem closedOrder_etale (hD : IsUnit (discriminant b f)) :
    Algebra.Etale (SignOrder b f I) (ClosedOrder b f I) := by
  letI : Algebra.Etale R (RootRing b f) := (finite_etale b f hD).2
  exact Algebra.Etale.of_equiv
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (RootRing b f) (contraction b f I)).symm

theorem closedOrder_faithfullyFlat [Nontrivial R] :
    Module.FaithfullyFlat (SignOrder b f I) (ClosedOrder b f I) := by
  letI : Module.FaithfullyFlat R (RootRing b f) := faithfullyFlat b f
  exact Module.FaithfullyFlat.of_linearEquiv (SignOrder b f I)
    ((SignOrder b f I) ⊗[R] RootRing b f)
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (RootRing b f) (contraction b f I)).toLinearEquiv

end DescendedOrder
end SelectedSignIdealDescent318

#print axioms SelectedSignIdealDescent318.linear_representative
#print axioms SelectedSignIdealDescent318.sign_involutive
#print axioms SelectedSignIdealDescent318.extension_contraction
#print axioms SelectedSignIdealDescent318.closedIdeal_eq
#print axioms SelectedSignIdealDescent318.closedOrder_etale
#print axioms SelectedSignIdealDescent318.closedOrder_faithfullyFlat
