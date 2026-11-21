module
public import SelectedOriginalCompactOverlapIdentity318
public import SelectedRationalGenericFromComplex318
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedRationalGenericFromComplex318 SelectedOriginalGenericChartClosures318
open SelectedOriginalGenericCompactNormal318

namespace SelectedRationalRootCompactInstall318

/-- The full rational generic root algebra of the same original p.
The definition does not take a factor or select a complex embedding. -/
abbrev RootField (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :=
  AdjoinRoot (p.map (rationalGenericMap N))

@[expose] def rationalAlgebra (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    Algebra ℚ (RootField N p) :=
  ((algebraMap QJ (RootField N p)).comp (algebraMap ℚ QJ)).toAlgebra

theorem rationalTower (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X]) :
    letI : Algebra ℚ (RootField N p) := rationalAlgebra N p
    IsScalarTower ℚ QJ (RootField N p) := by
  letI : Algebra ℚ (RootField N p) := rationalAlgebra N p
  exact IsScalarTower.of_algebraMap_eq' (R := ℚ) (S := QJ) (A := RootField N p) (by rfl)

/-- Actual compact normalization of the whole rational generic root
algebra, now a field. This keeps the originally specified projective
J-line and the standard two chart orders, not a stand-in compact curve. -/
@[expose] def compact (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hf : IsField (RootField N p)) : Scheme := by
  letI : Field (RootField N p) := hf.toField
  exact model (RootField N p)

@[expose] def compactJ (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hf : IsField (RootField N p)) : compact N p hf ⟶ ProjectiveJLine318.scheme ℚ := by
  letI : Field (RootField N p) := hf.toField
  exact modelMap (RootField N p)

theorem original_degree (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hp : p.Monic) : Module.finrank QJ (RootField N p) = p.natDegree := by
  change Module.finrank QJ (AdjoinRoot (p.map (rationalGenericMap N))) = _
  rw [Module.finrank_eq_card_basis
    (AdjoinRoot.powerBasis' (hp.map (rationalGenericMap N))).basis, Fintype.card_fin]
  change (p.map (rationalGenericMap N)).natDegree = p.natDegree
  exact hp.natDegree_map (rationalGenericMap N)

/-- No new trace bound is assumed: monic powers give finiteness of
the whole generic field extension and characteristic zero supplies
separability for the already-proved two-chart trace construction. -/
theorem compact_properties (N : ℕ) [NeZero N] (p : (OpenJModel318.Base N)[X])
    (hp : p.Monic) (hf : IsField (RootField N p)) :
    IsFinite (compactJ N p hf) ∧
    IsProper (compactJ N p hf ≫ ProjectiveJLine318.structureMap ℚ) ∧
    IsIntegral (compact N p hf) ∧
    ∀ x : compact N p hf, IsIntegrallyClosed ((compact N p hf).presheaf.stalk x) := by
  let K := RootField N p
  letI fK : Field K := hf.toField
  let aJ : Algebra QJ K := inferInstance
  letI aQ : Algebra ℚ K := rationalAlgebra N p
  let tQ : IsScalarTower ℚ QJ K := rationalTower N p
  letI hfin : FiniteDimensional QJ K := (hp.map (rationalGenericMap N)).finite_adjoinRoot
  let hsep : Algebra.IsSeparable QJ K := inferInstance
  exact ⟨@model_finite K fK aJ aQ tQ hfin hsep,
    @model_proper K fK aJ aQ tQ hfin hsep, model_integral K,
    @normal_stalk K fK aJ aQ tQ⟩

end SelectedRationalRootCompactInstall318

#print axioms SelectedRationalRootCompactInstall318.original_degree
#print axioms SelectedRationalRootCompactInstall318.compact_properties
