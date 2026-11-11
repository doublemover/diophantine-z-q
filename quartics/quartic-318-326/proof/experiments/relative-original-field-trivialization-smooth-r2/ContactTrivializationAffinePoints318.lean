module
public import ContactArbitraryFixedZero318
public section
noncomputable section
namespace ContactTrivializationAffinePoints318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactCoefficientNativeSections318
open ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
  (S : CommRingCat.{0}) [Algebra ℚ S] (f : R →ₐ[ℚ] S)
local instance : Algebra R S := f.toAlgebra
local notation "U" => ContactArbitraryNowhereZeroOpen318.locus R c L
local notation "N" => L' R S f c L
abbrev Points := AffineOpenAlgebraPoints318.Points R (parameterRing R c L) S U

@[expose] def zeroSections :
    {a : parameterRing R c L →ₐ[R] S //
      AffineOpenAlgebraPoints318.Factors R (parameterRing R c L) S U a} ≃
    {s : Γ(N.object,⊤) // IsEmpty ↑(ContactGlobalSectionZero318.scheme S c N s)} where
  toFun a := ⟨points R c L S f a.val,(ContactArbitraryFixedZero318.factor_iff_empty R c L S f a.val).mp a.property⟩
  invFun s := ⟨(points R c L S f).symm s.val,by
    apply (ContactArbitraryFixedZero318.factor_iff_empty R c L S f _).mpr
    rw [Equiv.apply_symm_apply]
    exact s.property⟩
  left_inv a := Subtype.ext ((points R c L S f).symm_apply_apply a.val)
  right_inv s := Subtype.ext ((points R c L S f).apply_symm_apply s.val)

/-- Genuine two-sided classification by actual scheme morphisms into the
constructed open, over the fixed original coefficient map, of entire
O-to-original-line trivializations. All affine tests are included. -/
@[expose] def equivalence : Points R c L S f ≃
    (SheafOfModules.unit (curve S c).ringCatSheaf ≅ N.object) :=
  (AffineOpenAlgebraPoints318.points R (parameterRing R c L) S U).trans
    ((zeroSections R c L S f).trans (ContactZeroEmptyTrivialization318.equivalence S c N))

/-- The scheme point retains its exact original section as frame value. -/
lemma value (x : Points R c L S f) :
    (equivalence R c L S f x).hom.app ⊤ 1=
      points R c L S f (AffineOpenAlgebraPoints318.coordinate R (parameterRing R c L) S U x) :=
  ContactZeroEmptyTrivialization318.frame_value S c N _ _

lemma determined_by_value (x y : Points R c L S f)
    (h : (equivalence R c L S f x).hom.app ⊤ 1=
      (equivalence R c L S f y).hom.app ⊤ 1) : x=y := by
  apply (equivalence R c L S f).injective
  apply Iso.ext
  exact ModuleTopExt318.ext h
end ContactTrivializationAffinePoints318
