module
public import SelectedOriginalCompactClassicalComparison318
public import SelectedCompactDifferentialSquare318
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public section
noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial KaehlerDifferential
open SelectedOriginalRationalOrdinary318 SelectedOriginalRationalOrdinaryRoot318
open SelectedRationalRootCompactInstall318 SelectedOriginalRationalOrdinaryGeometry318
open SelectedOriginalRationalOrdinaryPullback318
open SelectedOriginalCompactClassicalComparison318
open SelectedIntrinsicBaseLinear318 SelectedIntrinsicGlobalToAffine318
open SelectedNormalizedEtaleDJ318

namespace SelectedOriginalCompactClassicalDifferentials318

variable (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
local notation "B" => ordinaryRoot N p
abbrev jInRoot : B := algebraMap Base B jCoord

/-- The actual frame on the same ordinary algebra whose Spec was
identified with the original compact, normalized by the actual dJ. -/
@[expose] def rationalBaseFrame : KaehlerDifferential ℚ Base ≃ₗ[Base] Base := by
  letI : Algebra.Etale ℚ[X] Base := Algebra.Etale.of_isLocalizationAway denominator
  exact etaleFrame (polynomialEquiv ℚ)

theorem rationalBaseFrame_j :
    rationalBaseFrame (D ℚ Base jCoord) = 1 := by
  letI : Algebra.Etale ℚ[X] Base := Algebra.Etale.of_isLocalizationAway denominator
  change etaleFrame (polynomialEquiv ℚ) (D ℚ Base (algebraMap ℚ[X] Base X)) = 1
  rw [etaleFrame_D,polynomialEquiv_D,derivative_X,map_one]

variable (hp : p.Monic) (hd : IsUnit (AdjoinRoot.mk p p.derivative))

@[expose] def ordinaryFrame : KaehlerDifferential ℚ B ≃ₗ[B] B := by
  letI : Algebra.Etale Base B := ordinary_etale N p hp hd
  exact etaleFrame rationalBaseFrame

theorem ordinaryFrame_j : ordinaryFrame N p hp hd (D ℚ B (jInRoot N p)) = 1 := by
  letI : Algebra.Etale Base B := ordinary_etale N p hp hd
  change etaleFrame rationalBaseFrame (D ℚ B (algebraMap Base B jCoord)) = 1
  rw [etaleFrame_D,rationalBaseFrame_j,map_one]

/-- The coefficient is intrinsic on the literal chart, so no scalar
choice beyond its known j-structure can enter the determinant. -/
theorem ordinary_coefficient_iff (ω : KaehlerDifferential ℚ B) (r : B) :
    ω = r • D ℚ B (jInRoot N p) ↔ ordinaryFrame N p hp hd ω = r :=
  coefficient_iff _ _ (ordinaryFrame_j N p hp hd) ω r

section Compact

variable [Fact p.Monic]
variable (hf : IsField (genericRoot N p))
local notation "t" => ProjectiveJLine318.structureMap ℚ
local notation "pK" => (compactJ N p hf ≫ t)
local notation "a" => ordinaryEmbedding N p hf Fact.out hd

theorem actual_ordinary_Q :
    a ≫ pK = Spec.algebraMap ℚ B := by
  have h : (CommRingCat.ofHom (algebraMap ℚ ℚ[X]) ≫
      CommRingCat.ofHom (algebraMap ℚ[X] Base)) ≫ CommRingCat.ofHom (algebraMap Base B) =
        CommRingCat.ofHom (algebraMap ℚ B) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    simp only [CommRingCat.hom_comp,CommRingCat.hom_ofHom,RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply ℚ ℚ[X] Base,← IsScalarTower.algebraMap_apply ℚ Base B]
  rw [← Category.assoc,ordinary_over_J,Category.assoc]
  unfold baseEmbedding
  rw [Category.assoc,JLineAtlas318.chart_over_base,← Spec.map_comp,← Spec.map_comp,h]

variable {Y C : Scheme} (b : Y ⟶ V) (i : Y ⟶ C) [IsOpenImmersion i]
  (j : C ⟶ JLine) [IsFinite j] [IsIntegral C]
  (e : U N p ≅ Y) (he : e.hom ≫ b = q N p) (hi : i ≫ j = b ≫ baseEmbedding)
  (normal : ∀ W : C.Opens, IsAffineOpen W → Nonempty W → IsIntegrallyClosed Γ(C,W))

local notation "E" => classicalIso N p hf hd b i j e he hi normal
local notation "pC" => (j ≫ t)
local notation "c" => (e.hom ≫ i)

theorem classical_Q : (E).hom ≫ pC = pK := by
  rw [← Category.assoc,classicalIso_J]

include hd hf b he hi normal in
theorem classical_ordinary_Q : c ≫ pC = Spec.algebraMap ℚ B := by
  rw [← classicalIso_open N p hf hd b i j e he hi normal,Category.assoc,classical_Q]
  exact actual_ordinary_Q N p hd hf

local notation "uK" => actual_ordinary_Q N p hd hf
local notation "uC" => classical_ordinary_Q N p hd hf b i j e he hi normal
local notation "uQ" => classical_Q N p hd hf b i j e he hi normal

/-- Equality of the actual canonical restriction to the ordinary chart.
No supplied lattice, Petersson form, or choice of vector participates. -/
theorem same_canonical_restriction (ω : Sections pC) :
    restrict a pK uK (linearPullback pK pC E uQ ω) = restrict c pC uC ω :=
  SelectedCompactDifferentialSquare318.restrict_same
    pK pC c uC E uQ a uK (classicalIso_open N p hf hd b i j e he hi normal) ω

theorem same_literal_dJ_coefficient (ω : Sections pC) :
    ordinaryFrame N p Fact.out hd (restrict a pK uK (linearPullback pK pC E uQ ω)) =
      ordinaryFrame N p Fact.out hd (restrict c pC uC ω) :=
  congrArg (ordinaryFrame N p Fact.out hd)
    (same_canonical_restriction N p hd hf b i j e he hi normal ω)

variable {g : ℕ} {L : Type} [CommRing L] [Algebra ℚ L]

/-- An ordered minor from any actual list of center maps on this same
chart retains both its entries and determinant under the compact iso. -/
theorem same_ordered_minor
    (basis : Module.Basis (Fin g) ℚ (Sections pC)) (centerEval : Fin g → (B →ₐ[ℚ] L)) :
    (fun r s : Fin g => centerEval r (ordinaryFrame N p Fact.out hd
      (restrict a pK uK (transportedBasis pK pC E uQ basis s))) : Matrix (Fin g) (Fin g) L) =
    (fun r s : Fin g => centerEval r (ordinaryFrame N p Fact.out hd
      (restrict c pC uC (basis s)))) := by
  funext row col
  have hb : transportedBasis pK pC E uQ basis col = linearPullback pK pC E uQ (basis col) :=
    (transportedBasis_apply pK pC E uQ basis col).trans
      (linearPullback_apply pK pC E uQ (basis col)).symm
  have h₁ := congrArg (fun w : Sections pK =>
    centerEval row (ordinaryFrame N p Fact.out hd (restrict a pK uK w))) hb
  have h₂ := congrArg (fun x : B => centerEval row x)
    (same_literal_dJ_coefficient N p hd hf b i j e he hi normal (basis col))
  exact h₁.trans h₂

theorem same_ordered_det
    (basis : Module.Basis (Fin g) ℚ (Sections pC)) (centerEval : Fin g → (B →ₐ[ℚ] L)) :
    Matrix.det (fun r s : Fin g => centerEval r (ordinaryFrame N p Fact.out hd
      (restrict a pK uK (transportedBasis pK pC E uQ basis s))) : Matrix (Fin g) (Fin g) L) =
    Matrix.det (fun r s : Fin g => centerEval r (ordinaryFrame N p Fact.out hd
      (restrict c pC uC (basis s))) : Matrix (Fin g) (Fin g) L) :=
  congrArg (fun X : Matrix (Fin g) (Fin g) L => Matrix.det X)
    (same_ordered_minor N p hd hf b i j e he hi normal basis centerEval)

end Compact
end SelectedOriginalCompactClassicalDifferentials318

#print axioms SelectedOriginalCompactClassicalDifferentials318.ordinaryFrame_j
#print axioms SelectedOriginalCompactClassicalDifferentials318.same_canonical_restriction
#print axioms SelectedOriginalCompactClassicalDifferentials318.same_ordered_det
