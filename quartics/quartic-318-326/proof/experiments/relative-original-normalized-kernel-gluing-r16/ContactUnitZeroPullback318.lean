module
public import ContactClassifiedUnitZero318
public section
noncomputable section
namespace ContactUnitZeroPullback318
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
local notation "A" => parameterRing R c L
local instance : Algebra ℚ A := ((algebraMap R A).comp (algebraMap ℚ R)).toAlgebra
local instance : IsScalarTower ℚ R A := IsScalarTower.of_algebraMap_eq' rfl
variable (S : CommRingCat.{0}) [Algebra ℚ S] (g q : A →ₐ[ℚ] S) (u : Sˣ)
local notation "π" => ContactUniversalGlobalZero318.projection R c L hz
local notation "sp" a => Spec.map (CommRingCat.ofHom a.toRingHom)

/-- The SAME universal zero projection has isomorphic pullbacks along
unit-related actual parameter arrows. The comparison consumes the
original classified line and coefficient equality, not only fiber points. -/
@[expose] def iso (h : q=ContactClassifiedUnitZero318.scaledCoefficient R c L S g u) :
    pullback π (sp q) ≅ pullback π (sp g) := by
  subst q
  exact (ContactUniversalClassifiedZeroParameter318.iso R c L hz S
    (ContactClassifiedUnitZero318.scaledCoefficient R c L S g u)).symm ≪≫
    ContactClassifiedUnitZero318.iso R c L hz S g u ≪≫
    ContactUniversalClassifiedZeroParameter318.iso R c L hz S g

@[reassoc] lemma iso_projection
    (h : q=ContactClassifiedUnitZero318.scaledCoefficient R c L S g u) :
    (iso R c L hz S g q u h).hom ≫ pullback.snd π (sp g)=pullback.snd π (sp q) := by
  subst q
  simp only [iso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    ContactUniversalClassifiedZeroParameter318.iso_projection,
    ContactClassifiedUnitZero318.iso_projection]
  rw [← ContactUniversalClassifiedZeroParameter318.iso_projection R c L hz S
    (ContactClassifiedUnitZero318.scaledCoefficient R c L S g u),Iso.inv_hom_id_assoc]
end ContactUnitZeroPullback318
