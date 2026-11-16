module
public import ContactArbitraryZeroSpecialization318
public import ProperEmptyFamilyOpen318
public section
noncomputable section
namespace ContactArbitraryNowhereZeroOpen318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactArbitrarySectionParameter318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))

/-- An actual open subscheme of the arbitrary-line section parameter,
constructed by proper image of the full universal zero family. -/
abbrev locus : (parameterScheme R c L).Opens :=
  ProperEmptyFamilyOpen318.locus (ContactArbitraryUniversalZero318.projection R c L)
abbrev scheme := (locus R c L).toScheme
abbrev into : scheme R c L ⟶ parameterScheme R c L := (locus R c L).ι
instance : IsOpenImmersion (into R c L) := inferInstance

/-- Exact representability on ALL scheme tests of the empty universal-zero
condition. No flatness of the test morphism or vanishing of H1(L) is needed. -/
@[expose] def points (T : Scheme.{0}) : (T ⟶ scheme R c L) ≃
    {f : T ⟶ parameterScheme R c L //
      IsEmpty ↑(pullback (ContactArbitraryUniversalZero318.projection R c L) f)} :=
  ProperEmptyFamilyOpen318.points (ContactArbitraryUniversalZero318.projection R c L) T

lemma natural {T U : Scheme.{0}} (g : T ⟶ scheme R c L) (h : U ⟶ T) :
    (points R c L U (h ≫ g)).val=h ≫ (points R c L T g).val :=
  ProperEmptyFamilyOpen318.natural _ g h

lemma factor_iff {T : Scheme.{0}} (f : T ⟶ parameterScheme R c L) :
    (∃ g : T ⟶ scheme R c L,g ≫ into R c L=f) ↔
      IsEmpty ↑(pullback (ContactArbitraryUniversalZero318.projection R c L) f) :=
  ProperEmptyFamilyOpen318.factor_iff _ f
end ContactArbitraryNowhereZeroOpen318
