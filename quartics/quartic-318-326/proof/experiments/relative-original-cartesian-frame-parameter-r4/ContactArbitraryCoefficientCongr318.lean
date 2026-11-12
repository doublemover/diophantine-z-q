module
public import ContactArbitrarySectionParameter318
public import ContactGlobalSectionZero318
public section
noncomputable section
namespace ContactArbitraryCoefficientCongr318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (S : CommRingCat.{0}) [Algebra ℚ S] (f g : R →ₐ[ℚ] S)
  (a : letI : Algebra R S := f.toAlgebra; parameterRing R c L →ₐ[R] S)
  (b : letI : Algebra R S := g.toAlgebra; parameterRing R c L →ₐ[R] S)
@[expose] def lineIso (h : f=g) : (L' R S f c L).object ≅ (L' R S g c L).object :=
  eqToIso (congrArg (fun q : R →ₐ[ℚ] S => (L' R S q c L).object) h)
lemma sections (h : f=g) (ha : a.toRingHom=b.toRingHom) :
    (lineIso R c L S f g h).hom.app ⊤ (points R c L S f a)=points R c L S g b := by
  subst g
  have hab : a=b := AlgHom.ext (fun z => DFunLike.congr_fun ha z)
  subst b
  rfl
/-- Explicit coefficient equality transports the WHOLE zero scheme
condition, with both scalar structures retained in the theorem type. -/
lemma empty_iff (h : f=g) (ha : a.toRingHom=b.toRingHom) :
    IsEmpty ↑(ContactGlobalSectionZero318.scheme S c (L' R S f c L) (points R c L S f a)) ↔
    IsEmpty ↑(ContactGlobalSectionZero318.scheme S c (L' R S g c L) (points R c L S g b)) := by
  subst g
  have hab : a=b := AlgHom.ext (fun z => DFunLike.congr_fun ha z)
  subst b
  rfl
end ContactArbitraryCoefficientCongr318
