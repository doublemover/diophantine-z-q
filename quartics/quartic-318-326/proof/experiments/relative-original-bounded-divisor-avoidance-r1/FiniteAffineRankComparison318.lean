module
public import FiniteAffineAlgebra318
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public section
noncomputable section
namespace FiniteAffineRankComparison318
open AlgebraicGeometry CategoryTheory
universe u
variable (R : CommRingCat.{u}) {Z : Scheme.{u}} (p : Z ⟶ Spec R) [IsFinite p] [Flat p]
/-- Intrinsic scheme rank equals the stalk rank of the actual entire
family's affine algebra with its original coefficient map. -/
lemma rank_eq (x : PrimeSpectrum R) : p.finrank x=
    Module.rankAtStalk (FiniteAffineAlgebra318.ring R p) x := by
  let C := FiniteAffineAlgebra318.ring R p
  have hc : Spec.map (CommRingCat.ofHom (algebraMap R C))=Z.isoSpec.inv ≫ p :=
    FiniteAffineAlgebra318.spec_coefficient R p
  calc
    p.finrank x = (Z.isoSpec.inv ≫ p).finrank x := by rw [Scheme.Hom.finrank_comp_left_of_isIso]
    _ = (Spec.map (CommRingCat.ofHom (algebraMap R C))).finrank x :=
      congrArg (fun f => f.finrank x) hc.symm
    _ = Module.rankAtStalk C x := Scheme.Hom.finrank_SpecMap_algebraMap R C x
end FiniteAffineRankComparison318
