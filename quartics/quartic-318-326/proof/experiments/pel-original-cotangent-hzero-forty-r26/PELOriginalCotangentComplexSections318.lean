module
public import PELOriginalCotangentSkyscrapers318
public import ClosedComplexStalkResidue318
public import SimpleLocalComplexDimension318
public import AbelianProductCoordinates318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace PELOriginalCotangentComplexSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalCommonContactBase318 FourRootGluedDerivativeIdeal318
open PELOriginalCotangentSectionGerms318 PELOriginalCotangentSkyscrapers318
abbrev structure := FourRootGluedScheme318.structureMap branches
local instance proper : IsProper structure := FourRootActualProperModel318.proper branches
instance sectionModule : Module ℂ H0 := CanonicalComplexStalkScalars318.sectionModule structure omega
instance stalkAlgebra (z : zeroScheme branches) : Algebra ℂ (X.presheaf.stalk (into branches z)) :=
  CanonicalComplexStalkScalars318.stalkAlgebra structure (into branches z)
instance stalkModule (z : zeroScheme branches) : Module ℂ (Stalk z) :=
  CanonicalComplexStalkScalars318.stalkModule structure omega (into branches z)
instance stalkTower (z : zeroScheme branches) :
    IsScalarTower ℂ (X.presheaf.stalk (into branches z)) (Stalk z) :=
  CanonicalComplexStalkScalars318.stalkTower structure omega (into branches z)
/-- Every actual branch stalk has complex dimension1 for its genuine
structural scalars; this uses the residue-field scalar square, not local
ring length alone. -/
theorem stalk_finrank (z : zeroScheme branches) : Module.finrank ℂ (Stalk z) = 1 :=
  SimpleLocalComplexDimension318.finrank_one
    (PELOriginalGlobalCotangentLength318.on_zero z)
    (ClosedComplexStalkResidue318.algebraMap_bijective structure _ (support_point_closed z))
instance stalk_finite (z : zeroScheme branches) : Module.Finite ℂ (Stalk z) :=
  SimpleLocalComplexDimension318.finite
    (PELOriginalGlobalCotangentLength318.on_zero z)
    (ClosedComplexStalkResidue318.algebraMap_bijective structure _ (support_point_closed z))
/-- The actual global-germ map is linear for the SAME structural complex
scalars on the original sections and every actual local stalk. -/
@[expose] def linearGerms : H0 →ₗ[ℂ] ∀ z : zeroScheme branches, Stalk z :=
  LinearMap.pi (fun z => CanonicalComplexStalkScalars318.germ structure omega (into branches z))
@[expose] def additiveEquiv : H0 ≃+ ∀ z : zeroScheme branches, Stalk z :=
  (globalSectionsIso ≪≫ AbelianProductCoordinates318.piIso
    (fun z : zeroScheme branches => additiveSheaf.obj.stalk (into branches z))).addCommGroupIsoToAddEquiv
lemma additiveEquiv_apply (s : H0) (z : zeroScheme branches) :
    additiveEquiv s z = omega.presheaf.germ ⊤ (into branches z) trivial s := by
  change (AbelianProductCoordinates318.piIso _).hom (globalSectionsIso.hom s) z = _
  rw [AbelianProductCoordinates318.hom_apply]
  exact congrArg (fun f : additiveSheaf.obj.obj (.op ⊤) ⟶
    additiveSheaf.obj.stalk (into branches z) => f s) (globalSectionsIso_hom_π z)
theorem linearGerms_bijective : Function.Bijective linearGerms := by
  have he : (linearGerms : H0 → ∀ z : zeroScheme branches, Stalk z) = additiveEquiv := by
    funext s z
    exact (additiveEquiv_apply s z).symm
  rw [he]
  exact additiveEquiv.bijective
/-- Canonical COMPLEX-linear global-section/stalk decomposition. -/
@[expose] def globalLinearEquiv : H0 ≃ₗ[ℂ] ∀ z : zeroScheme branches, Stalk z :=
  LinearEquiv.ofBijective linearGerms linearGerms_bijective
instance finite : Module.Finite ℂ H0 := Module.Finite.equiv globalLinearEquiv.symm
/-- Actual H0 of the intrinsic relative cotangent, with its original
structural complex scalars, has dimension40. This is distinct from
H0(O_Z) and is proved through the genuine global-germ isomorphism. -/
theorem hzero_finrank_forty : Module.finrank ℂ H0 = 40 := by
  classical
  letI : Fintype (zeroScheme branches) := Fintype.ofFinite _
  rw [globalLinearEquiv.finrank_eq,Module.finrank_pi_fintype]
  simp_rw [stalk_finrank]
  have hc : Fintype.card (zeroScheme branches) = 40 := by
    simpa only [Nat.card_eq_fintype_card] using PELOriginalZeroAllPoints318.card_forty
  simp [hc]
end PELOriginalCotangentComplexSections318
