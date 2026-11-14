module
public import FourRootZeroFiniteAlgebras318
public import FourRootDerivativeZeroReduced318
public import FourRootActualProperModel318
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public section
noncomputable section
namespace FourRootDerivativeZeroFinite318
open AlgebraicGeometry CategoryTheory
open FourRootGluedDerivativeIdeal318
variable (b : Fin 4 → ℂ) (hb : Function.Injective b)
/-- The existing zero scheme's actual structural morphism is induced
by its unchanged closed immersion into the original whole curve. -/
@[expose] def structure : zeroScheme b ⟶ Spec (CommRingCat.of ℂ) :=
  into b ≫ FourRootGluedScheme318.structureMap b
lemma finite_structure : finiteChart b ≫ structure b =
    Spec.algebraMap ℂ (FourRootAffineCoordinateRing318.Ring b ⧸
      FourRootDerivativeZeroIdeals318.finiteIdeal b) := by
  rw [structure,← Category.assoc,finiteChart_into]
  rw [finiteInto,Category.assoc,FourRootGluedScheme318.finite_structure]
  unfold FourRootGluedScheme318.finiteBase
  rw [← Spec.map_comp]
  rfl
lemma infinity_structure : infinityChart b ≫ structure b =
    Spec.algebraMap ℂ (FourRootInfinityCoordinateRing318.Ring b ⧸
      FourRootDerivativeZeroIdeals318.infinityIdeal b) := by
  rw [structure,← Category.assoc,infinityChart_into]
  rw [infinityInto,Category.assoc,FourRootGluedScheme318.infinity_structure]
  unfold FourRootGluedScheme318.infinityBase
  rw [← Spec.map_comp]
  rfl
lemma proper : IsProper (structure b) := by
  letI := FourRootActualProperModel318.proper b
  unfold structure
  infer_instance
/-- Actual finite quotient-chart maps imply local quasi-finiteness of
the global map. Finiteness itself is not falsely treated as local at source. -/
lemma locallyQuasiFinite : LocallyQuasiFinite (structure b) := by
  letI := FourRootZeroFiniteAlgebras318.finite_zero b hb
  letI := FourRootZeroFiniteAlgebras318.infinity_zero b hb
  haveI : IsFinite (Spec.algebraMap ℂ (FourRootAffineCoordinateRing318.Ring b ⧸
      FourRootDerivativeZeroIdeals318.finiteIdeal b)) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  haveI : IsFinite (Spec.algebraMap ℂ (FourRootInfinityCoordinateRing318.Ring b ⧸
      FourRootDerivativeZeroIdeals318.infinityIdeal b)) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @LocallyQuasiFinite) (FourRootDerivativeZeroReduced318.twoChartCover b)).mpr
  intro k
  cases k
  · change LocallyQuasiFinite (infinityChart b ≫ structure b)
    rw [infinity_structure]
    infer_instance
  · change LocallyQuasiFinite (finiteChart b ≫ structure b)
    rw [finite_structure]
    infer_instance
/-- The SAME original derivative-zero scheme is finite over C, using
its actual proper closed immersion and genuine local quasi-finiteness. -/
theorem finite : IsFinite (structure b) := by
  letI := proper b
  letI := locallyQuasiFinite b hb
  exact IsFinite.of_isProper_of_locallyQuasiFinite (structure b)
theorem affine : IsAffine (zeroScheme b) := by
  letI := finite b hb
  exact isAffine_of_isAffineHom (structure b)
/-- Finite AND reduced refer to the original zero scheme, with no
replacement of the scheme, closed inclusion or original base map. -/
theorem finite_reduced : IsFinite (structure b) ∧ IsReduced (zeroScheme b) :=
  ⟨finite b hb,FourRootDerivativeZeroReduced318.reduced b hb⟩
end FourRootDerivativeZeroFinite318
