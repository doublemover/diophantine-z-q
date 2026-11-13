module
public import ContactRationalFieldSourceRebuild318
public import ContactArbitraryNowhereZeroOpen318
public import Mathlib.AlgebraicGeometry.ResidueField
public section
noncomputable section
namespace ContactNowhereZeroResidueSourceRebuild318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "N" => ContactArbitraryNowhereZeroOpen318.scheme R c L
local notation "j" => ContactArbitraryNowhereZeroOpen318.into R c L
local notation "A" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ A :=
  ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
/-- Every point of the actual original nowhere-zero OPEN gives a
native residue test, with its rational structure induced by that exact map. -/
def data (y : N) :
    {a : Spec (N.residueField y) ⟶ ContactOriginalGlobalKernelNormalizationRebuild318.source R c L //
      a ≫ ContactOriginalGlobalKernelNormalizationRebuild318.original R c L =
        N.fromSpecResidueField y ≫ j} := by
  let K := N.residueField y
  let t : Spec K ⟶ N := N.fromSpecResidueField y
  let b : A ⟶ K := Spec.preimage (t ≫ j)
  letI : Algebra ℚ K := (b.hom.comp (algebraMap ℚ A)).toAlgebra
  let g : A →ₐ[ℚ] K := ContactOriginalRelativeOverlap318.rationalMap (t ≫ j)
  have hg : Spec.map (CommRingCat.ofHom g.toRingHom) = t ≫ j :=
    ContactOriginalRelativeOverlap318.rationalMap_spec _
  have he : IsEmpty ↑(pullback (ContactArbitraryUniversalZero318.projection R c L)
      (Spec.map (CommRingCat.ofHom g.toRingHom))) :=
    (ContactArbitraryNowhereZeroOpen318.factor_iff R c L _).mp ⟨t,hg.symm⟩
  let a := ContactRationalFieldSourceRebuild318.data R c L K g he
  exact ⟨a.val,a.property.trans hg⟩
end ContactNowhereZeroResidueSourceRebuild318
