module
public import CTActualSelectedImageOrderLocal318
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public section
noncomputable section

namespace CTActualSelectedResidueGalois318

open CTActualSelectedPadicLayer318 CTActualSelectedPadicValuation318
open CTActualSelectedImageOrderLocal318 CTActualSelectedOrderFraction318
open CTPadicSelectedValuationRing318
open IsLocalRing
open scoped CTPadicSelectedValuationRing318 nonZeroDivisors

variable (p : ℕ) [Fact p.Prime] (M : GlobalLayer)
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
variable (w : Valuation (Pbar p) Γ) [(Padic.mulValuation (p := p)).HasExtension w]
variable (hD : ¬(p : ℤ) ∣ NumberField.discr M.toIntermediateField)

local notation "R" => ℤ_[p]
local notation "K" => ℚ_[p]
local notation "L" => localField p M
local notation "S" => selectedIntegers p M w
local notation "k" => ResidueField R
local notation "l" => ResidueField S
local notation "GalL" => (L ≃ₐ[K] L)
local notation "Galbar" => (l ≃ₐ[k] l)

/-- Integrality is checked in the very same actual valuation subring,
not in a different local field or a chosen isomorphic valuation ring. -/
@[expose] def integerMap (σ : GalL) : S →ₐ[R] S where
  toFun x := ⟨σ (x : L), by
    have hx : IsIntegral R (x : L) := selected_forward_integral p M w hD _ x.property
    have hy : IsIntegral R (σ (x : L)) := hx.map (σ.restrictScalars R)
    let v := selectedLayerValuation p M w
    exact (v.valuationSubring.integers.isIntegral_iff_v_le_one).1 hy.tower_top⟩
  map_one' := Subtype.ext (map_one σ)
  map_mul' x y := Subtype.ext (map_mul σ (x : L) (y : L))
  map_zero' := Subtype.ext (map_zero σ)
  map_add' x y := Subtype.ext (map_add σ (x : L) (y : L))
  commutes' r := by
    apply Subtype.ext
    change σ (algebraMap S L (algebraMap R S r)) =
      algebraMap S L (algebraMap R S r)
    rw [← IsScalarTower.algebraMap_apply R S L]
    exact (σ.restrictScalars R).commutes r

def integerAut (σ : GalL) : S ≃ₐ[R] S :=
  AlgEquiv.ofAlgHom (integerMap p M w hD σ) (integerMap p M w hD σ.symm)
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      exact σ.apply_symm_apply (x : L))
    (by
      apply AlgHom.ext
      intro x
      apply Subtype.ext
      exact σ.symm_apply_apply (x : L))

@[simp] theorem integerAut_coe (σ : GalL) (x : S) :
    (integerAut p M w hD σ x : L) = σ (x : L) := by
  rfl

/-- Canonical reduction of actual local conjugation on the inherited
valuation integers. Base scalar ring and target scalar field are the
literal residue fields. -/
def residueRestriction : GalL →* Galbar where
  toFun σ := ResidueField.mapAlgEquiv' (integerAut p M w hD σ)
  map_one' := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := (residue_surjective (R := S)) z
    rw [ResidueField.mapAlgEquiv'_residue,AlgEquiv.one_apply]
    apply congrArg (residue S)
    apply Subtype.ext
    rw [integerAut_coe,AlgEquiv.one_apply]
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨x,rfl⟩ := (residue_surjective (R := S)) z
    simp only [AlgEquiv.mul_apply,ResidueField.mapAlgEquiv'_residue]
    apply congrArg (residue S)
    apply Subtype.ext
    simp only [integerAut_coe,AlgEquiv.mul_apply]

theorem residueRestriction_apply (σ : GalL) (x : S) :
    residueRestriction p M w hD σ (residue S x) =
      residue S (integerAut p M w hD σ x) :=
  ResidueField.mapAlgEquiv'_residue (integerAut p M w hD σ) x

private theorem selected_intClosure : IsIntegralClosure S R L :=
  actual_isIntegralClosure (selectedLayerValuation p M w)
    (selected_forward_integral p M w hD)

/-- Same integral basis controls both the selected fraction field and
the actual residue field. In particular, no unramified-degree or
residual-normality comparison has been supplied as a premise. -/
theorem residue_finite_finrank :
    Finite l ∧ Module.finrank K L = Module.finrank k l := by
  letI := selected_intClosure p M w hD
  obtain ⟨n,b⟩ := actualIntegralBasis (selectedLayerValuation p M w)
  have hI := actual_maximalIdeal_map p M w hD
  let c := CTUnramifiedResidueBasis318.residueBasis hI b
  letI : Fintype k := Fintype.ofEquiv (ZMod p) PadicInt.residueField.symm.toEquiv
  letI : Fintype l := Fintype.ofEquiv (Fin n → k) c.equivFun.symm.toEquiv
  letI : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L :=
    IsIntegralClosure.isLocalization R K L S
  let d := b.localizationLocalization K (nonZeroDivisors R) L
  refine ⟨inferInstance,?_⟩
  rw [Module.finrank_eq_card_basis d,Module.finrank_eq_card_basis c]

/-- Two local automorphisms with the same residue reduction agree:
unique lift through every power of the actual maximal ideal, then
actual fraction-ring extension. -/
theorem residueRestriction_injective : Function.Injective (residueRestriction p M w hD) := by
  letI := selected_intClosure p M w hD
  letI : Module.Finite R S := IsIntegralClosure.finite R K L S
  letI : Finite l := (residue_finite_finrank p M w hD).1
  letI : IsGalois k l := inferInstance
  have hI := actual_maximalIdeal_map p M w hD
  letI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.of_map_maximalIdeal hI
  letI : IsAdicComplete (maximalIdeal R) R := CTPadicAdicFiniteComplete318.padic_adic_complete p
  have hC : IsAdicComplete (maximalIdeal S) S := by
    rw [← hI,IsAdicComplete.map_algebraMap_iff]
    exact CTPadicAdicFiniteComplete318.finite_module_complete _
  have hSep : (⨅ n : ℕ, maximalIdeal S ^ n) = ⊥ := by
    simpa only [smul_eq_mul,Ideal.mul_top] using hC.toIsHausdorff.iInf_pow_smul
  intro σ τ he
  have hEq : (integerAut p M w hD σ).toAlgHom = (integerAut p M w hD τ).toAlgHom := by
    apply Algebra.FormallyUnramified.ext_of_iInf (I := maximalIdeal S) hSep
    intro x
    have hx := DFunLike.congr_fun he (residue S x)
    rwa [residueRestriction_apply,residueRestriction_apply] at hx
  apply AlgEquiv.toRingEquiv_injective
  apply RingEquiv.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := S)
  intro x
  have hx := DFunLike.congr_fun hEq x
  have h := congrArg (algebraMap S L) hx
  change σ (algebraMap S L x) = τ (algebraMap S L x)
  simpa only [ValuationSubring.algebraMap_apply,integerAut_coe] using h

/-- Literal unramified reduction, not an abstract cyclic isomorphism.
Normality/separability of the finite residue extension come from the
splitting polynomial X^(#l)−X, via the pinned finite field instance. -/
def residueGaloisEquiv : GalL ≃* Galbar := by
  letI : Finite l := (residue_finite_finrank p M w hD).1
  letI : IsGalois k l := inferInstance
  have hc : Nat.card Galbar = Nat.card GalL := by
    rw [IsGalois.card_aut_eq_finrank k l,IsGalois.card_aut_eq_finrank K L]
    exact (residue_finite_finrank p M w hD).2.symm
  exact MulEquiv.ofBijective (residueRestriction p M w hD)
    ((residueRestriction_injective p M w hD).bijective_of_nat_card_le hc.le)

theorem residueGaloisEquiv_apply (σ : GalL) (x : S) :
    residueGaloisEquiv p M w hD σ (residue S x) =
      residue S (integerAut p M w hD σ x) :=
  residueRestriction_apply p M w hD σ x

end CTActualSelectedResidueGalois318
