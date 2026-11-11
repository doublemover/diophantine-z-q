module
public import ContactNormalizedOriginalCurve318
public section
noncomputable section
namespace ContactUnitZeroOriginal318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
local notation "A" => CommRingCat.of (parameterRing R c L)
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g q : A →ₐ[ℚ] S) (u : Sˣ)
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "into" => ContactUniversalGlobalZero318.into R c L hz
local notation "base" => ContactRelativeCoefficientChange318.curveMap R A (parameterCoefficient R c L) c

/-- Unit-related pullbacks of the SAME universal zero preserve the map
to the ORIGINAL curve over R. The two coefficient maps are compared
explicitly; equality only of their parameter projections is insufficient. -/
@[reassoc] lemma original
    (h : q=ContactClassifiedUnitZero318.scaledCoefficient R c L S g u) :
    (ContactUnitZeroPullback318.iso R c L hz S g q u h).hom ≫
      pullback.fst _ _ ≫ into ≫ base=
    pullback.fst π (Spec.map (CommRingCat.ofHom q.toRingHom)) ≫ into ≫ base := by
  subst q
  apply (cancel_epi (ContactUniversalClassifiedZeroParameter318.iso R c L hz S
    (ContactClassifiedUnitZero318.scaledCoefficient R c L S g u)).hom).1
  simp only [ContactUnitZeroPullback318.iso,Iso.trans_hom,Iso.symm_hom,
    Category.assoc,Iso.hom_inv_id_assoc]
  rw [ContactNormalizedOriginalCurve318.universal_ambient_assoc,
    ContactNormalizedOriginalCurve318.universal_ambient_assoc,
    ContactClassifiedUnitZero318.iso_into_assoc,
    ContactCoefficientWholeOpens318.composition,
    ContactCoefficientWholeOpens318.composition,
    ContactClassifiedUnitZero318.coefficient_base]
end ContactUnitZeroOriginal318
