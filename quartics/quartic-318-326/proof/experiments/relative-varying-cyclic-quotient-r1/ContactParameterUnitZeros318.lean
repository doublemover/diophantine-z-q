module
public import ProjectiveParameterUnitAction318
public import ContactZeroUnitScaling318
public import ContactOriginalSectionParameter318
public section
noncomputable section
namespace ContactParameterUnitZeros318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactOriginalSectionParameter318
open ContactCoefficientNativeSections318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
local instance : Module.Finite R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).1
local instance : Module.Projective R Γ(L.object,⊤) :=
  (ContactRelativeFiniteProjectiveHZero318.finite_projective R c L hz).2
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local notation "N" => L' R S f c L
local instance : Module S Γ(N.object,⊤) := OriginalCoefficientCohomology318.sectionModule S
  (ContactRelativeStructuralHOne318.projection S c) N ⊤
variable (u : Sˣ) (a : parameterRing R c L →ₐ[R] S)
local notation "a'" => ProjectiveParameterUnitAction318.pointScale R Γ(L.object,⊤) S (u:S) a

/-- ALL coefficient-test units act on the original represented global
sections, with no assumption that the unit descends to the ground ring. -/
lemma classified_section : points R c L hz S f a'=(u:S) • points R c L hz S f a := by
  change (ContactRelativeHZeroBaseChange318.equivalence R S f c L hz)
    (ProjectiveSectionParameter318.points R Γ(L.object,⊤) S a')=_
  rw [ProjectiveParameterUnitAction318.points_pointScale,map_smul]
  rfl

/-- The actual whole zero scheme of the classified original section is
invariant under this relative unit action. This is scheme-theoretic,
not just equality of supports or a count of geometric points. -/
@[expose] def zeroIso : ContactGlobalSectionZero318.scheme S c N (points R c L hz S f a') ≅
    ContactGlobalSectionZero318.scheme S c N (points R c L hz S f a) :=
  (eqToIso (congrArg (ContactGlobalSectionZero318.scheme S c N)
    (classified_section R c L hz S f u a))).trans
    (ContactZeroUnitScaling318.iso S c N u (points R c L hz S f a))

private lemma equality_into (s t : Γ(N.object,⊤)) (h : s=t) :
    (eqToIso (congrArg (ContactGlobalSectionZero318.scheme S c N) h)).hom ≫
      ContactGlobalSectionZero318.into S c N t=ContactGlobalSectionZero318.into S c N s := by
  subst t
  simp only [eqToIso_refl,Iso.refl_hom,Category.id_comp]

@[reassoc] lemma zeroIso_into : (zeroIso R c L hz S f u a).hom ≫
    ContactGlobalSectionZero318.into S c N (points R c L hz S f a)=
    ContactGlobalSectionZero318.into S c N (points R c L hz S f a') := by
  unfold zeroIso
  simp only [Iso.trans_hom,Category.assoc,ContactZeroUnitScaling318.iso_into]
  exact equality_into R c L S f _ _ (classified_section R c L hz S f u a)


@[reassoc] lemma zeroIso_projection : (zeroIso R c L hz S f u a).hom ≫
    ContactGlobalResidueFlat318.projection S c N (points R c L hz S f a)=
    ContactGlobalResidueFlat318.projection S c N (points R c L hz S f a') := by
  rw [ContactGlobalResidueFlat318.projection,← Category.assoc,zeroIso_into]
  rfl
end ContactParameterUnitZeros318
