module
public import FiniteAlgebraSpectrumBound318
public import FiniteAffineAlgebra318
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public section
noncomputable section
namespace FiniteSchemePointBound318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y : Scheme.{u}}
@[expose] def points (e : X ≅ Y) : X ≃ Y where
  toFun := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun k : X ⟶ X => k x) e.hom_inv_id
  right_inv y := congrArg (fun k : Y ⟶ Y => k y) e.inv_hom_id
variable (K : Type u) [Field K] (f : X ⟶ Spec (CommRingCat.of K)) [IsFinite f]
local instance sourceAffine : IsAffine X := isAffine_of_isAffineHom f
instance finite_points : Finite X := by
  let C := FiniteAffineAlgebra318.ring (CommRingCat.of K) f
  letI : IsArtinianRing C := isArtinian_of_tower K inferInstance
  exact Finite.of_injective (points X.isoSpec) (points X.isoSpec).injective
/-- Actual topological point count of a finite scheme over a field is
bounded by the actual structural rank, without etaleness or reducedness. -/
lemma card_le_rank [Flat f] : Nat.card X≤f.finrank (IsLocalRing.closedPoint K) := by
  let C := FiniteAffineAlgebra318.ring (CommRingCat.of K) f
  have hcoef : Spec.map (CommRingCat.ofHom (algebraMap K C))=X.isoSpec.inv ≫ f :=
    FiniteAffineAlgebra318.spec_coefficient (CommRingCat.of K) f
  calc
    Nat.card X = Nat.card (PrimeSpectrum C) := Nat.card_congr (points X.isoSpec)
    _ ≤ Module.finrank K C := FiniteAlgebraSpectrumBound318.card_spectrum_le K C
    _ = (Spec.map (CommRingCat.ofHom (algebraMap K C))).finrank (IsLocalRing.closedPoint K) := by
      rw [Scheme.Hom.finrank_SpecMap_algebraMap,Module.rankAtStalk_eq_finrank_of_free]
      rfl
    _ = f.finrank (IsLocalRing.closedPoint K) := by
      rw [hcoef,Scheme.Hom.finrank_comp_left_of_isIso]
end FiniteSchemePointBound318
