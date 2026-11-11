module
public import ContactQuotientTripleData318
public section
noncomputable section
namespace ContactQuotientTripleScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318 ContactQuotientOverlapOpen318
variable (c : Fin 4 → ℚˣ) (a b d : Chart) (n : ℕ)
abbrev scheme := pullback (parameterOpen c a b n).ι (parameterOpen c a d n).ι
abbrev first : scheme c a b d n ⟶ (parameterOpen c a b n).toScheme := pullback.fst _ _
abbrev second : scheme c a b d n ⟶ (parameterOpen c a d n).toScheme := pullback.snd _ _
@[expose] def structureMap : scheme c a b d n ⟶ Spec (CommRingCat.of ℚ) :=
  first c a b d n ≫ ContactQuotientOverlapSchemeRule318.structureMap c a b n
@[reassoc] lemma second_over : second c a b d n ≫ ContactQuotientOverlapSchemeRule318.structureMap c a d n=
    structureMap c a b d n := by
  change second c a b d n ≫ ((parameterOpen c a d n).ι ≫ _)=(first c a b d n) ≫ ((parameterOpen c a b n).ι ≫ _)
  rw [← Category.assoc,← Category.assoc,pullback.condition]
variable (S : CommRingCat.{0}) [Algebra ℚ S]
abbrev Test := RelativeAffineTestRule318.Test ℚ (structureMap c a b d n) S
@[expose] def firstPoint (x : Test c a b d n S) : Point c a b n S :=
  ⟨x.val ≫ first c a b d n,by simpa only [Category.assoc] using x.property⟩
@[expose] def secondPoint (x : Test c a b d n S) : Point c a d n S :=
  ⟨x.val ≫ second c a b d n,by
    change (x.val ≫ second c a b d n) ≫ ContactQuotientOverlapSchemeRule318.structureMap c a d n=_
    rw [Category.assoc,second_over]
    exact x.property⟩
lemma underlying_eq (x : Test c a b d n S) : underlying c a b n S (firstPoint c a b d n S x)=
    underlying c a d n S (secondPoint c a b d n S x) := by
  apply Subtype.ext
  change (x.val ≫ first c a b d n) ≫ (parameterOpen c a b n).ι=
    (x.val ≫ second c a b d n) ≫ (parameterOpen c a d n).ι
  rw [Category.assoc,Category.assoc,pullback.condition]
end ContactQuotientTripleScheme318
