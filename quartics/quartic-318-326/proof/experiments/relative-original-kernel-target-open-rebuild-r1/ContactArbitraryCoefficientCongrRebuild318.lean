module
public import ContactArbitrarySectionParameter318
public import ContactZeroLineIso318
public section
noncomputable section
namespace ContactArbitraryCoefficientCongrRebuild318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
variable (S : CommRingCat.{0}) [Algebra ℚ S] (f g : R →ₐ[ℚ] S)
  (a : letI : Algebra R S := f.toAlgebra; ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] S)
  (b : letI : Algebra R S := g.toAlgebra; ContactArbitrarySectionParameter318.parameterRing R c L →ₐ[R] S)
/-- Credited adaptation of ContactSectionCoefficientCongr318 to the
actual arbitrary-line kernel parameter; no H1 vanishing is required. -/
def lineIso (h : f=g) : (L' R S f c L).object ≅ (L' R S g c L).object :=
  eqToIso (congrArg (fun q : R →ₐ[ℚ] S => (L' R S q c L).object) h)
lemma sections (h : f=g) (ha : a.toRingHom=b.toRingHom) :
    (lineIso R c L S f g h).hom.app ⊤ (ContactArbitrarySectionParameter318.points R c L S f a) =
      ContactArbitrarySectionParameter318.points R c L S g b := by
  subst g
  have hab : a=b := AlgHom.ext (fun z => DFunLike.congr_fun ha z)
  subst b
  rfl
/-- Exact whole zero-scheme comparison retains actual coefficient arrows
and their induced original line modules before comparing sections. -/
def zeroIso (h : f=g) (ha : a.toRingHom=b.toRingHom) :
    ContactGlobalSectionZero318.scheme S c (L' R S g c L)
      (ContactArbitrarySectionParameter318.points R c L S g b) ≅
    ContactGlobalSectionZero318.scheme S c (L' R S f c L)
      (ContactArbitrarySectionParameter318.points R c L S f a) :=
  eqToIso (congrArg (ContactGlobalSectionZero318.scheme S c (L' R S g c L))
    (sections R c L S f g a b h ha).symm) ≪≫
    ContactZeroLineIso318.iso S c (L' R S f c L) (L' R S g c L)
      (lineIso R c L S f g h) (ContactArbitrarySectionParameter318.points R c L S f a)
end ContactArbitraryCoefficientCongrRebuild318
