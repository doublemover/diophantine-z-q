module
public import ContactOriginalSectionParameter318
public import ContactZeroLineIso318
public section
noncomputable section
namespace ContactSectionCoefficientCongr318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (hz : ∀ x : NonreducedLineMayerVietoris318.H1 L,x=0)
local instance : Module R Γ(L.object,⊤) := OriginalCoefficientCohomology318.sectionModule R
  (ContactRelativeStructuralHOne318.projection R c) L ⊤
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f g : R →ₐ[ℚ] S)
  (a : letI : Algebra R S := f.toAlgebra; ContactOriginalSectionParameter318.parameterRing R c L →ₐ[R] S)
  (b : letI : Algebra R S := g.toAlgebra; ContactOriginalSectionParameter318.parameterRing R c L →ₐ[R] S)

/-- Equality of the actual coefficient arrows identifies the actual
pulled line modules, before either global-section presentation is used. -/
@[expose] def lineIso (h : f=g) : (L' R S f c L).object ≅ (L' R S g c L).object :=
  eqToIso (congrArg (fun q : R →ₐ[ℚ] S => (L' R S q c L).object) h)

/-- Scalar structures on the two test point types are kept explicit.
Equality of underlying actual ring maps, not a hidden instance change,
then identifies the classified ORIGINAL sections through the line iso. -/
lemma sections (h : f=g) (ha : a.toRingHom=b.toRingHom) :
    (lineIso R c L S f g h).hom.app ⊤ (ContactOriginalSectionParameter318.points R c L hz S f a)=
      ContactOriginalSectionParameter318.points R c L hz S g b := by
  subst g
  have hab : a=b := AlgHom.ext (fun z => DFunLike.congr_fun ha z)
  subst b
  rfl

private lemma equality_into (N : Line (curve S c)) (s t : Γ(N.object,⊤)) (h : s=t) :
    (eqToIso (congrArg (ContactGlobalSectionZero318.scheme S c N) h)).hom ≫
      ContactGlobalSectionZero318.into S c N t=ContactGlobalSectionZero318.into S c N s := by
  subst t
  simp only [eqToIso_refl,Iso.refl_hom,Category.id_comp]

/-- The coefficient comparison induces an actual zero-scheme comparison,
retaining the original ambient curve, not replacing it by an isomorphic
curve chosen only by its points. -/
@[expose] def zeroIso (h : f=g) (ha : a.toRingHom=b.toRingHom) :
    ContactGlobalSectionZero318.scheme S c (L' R S g c L)
      (ContactOriginalSectionParameter318.points R c L hz S g b) ≅
    ContactGlobalSectionZero318.scheme S c (L' R S f c L)
      (ContactOriginalSectionParameter318.points R c L hz S f a) :=
  eqToIso (congrArg (ContactGlobalSectionZero318.scheme S c (L' R S g c L))
    (sections R c L hz S f g a b h ha).symm) ≪≫
    ContactZeroLineIso318.iso S c (L' R S f c L) (L' R S g c L)
      (lineIso R c L S f g h) (ContactOriginalSectionParameter318.points R c L hz S f a)

@[reassoc] lemma zeroIso_into (h : f=g) (ha : a.toRingHom=b.toRingHom) :
    (zeroIso R c L hz S f g a b h ha).hom ≫
      ContactGlobalSectionZero318.into S c (L' R S f c L)
        (ContactOriginalSectionParameter318.points R c L hz S f a)=
    ContactGlobalSectionZero318.into S c (L' R S g c L)
      (ContactOriginalSectionParameter318.points R c L hz S g b) := by
  rw [zeroIso,Iso.trans_hom,Category.assoc,ContactZeroLineIso318.iso_into]
  exact equality_into c S _ _ _ (sections R c L hz S f g a b h ha).symm
end ContactSectionCoefficientCongr318
