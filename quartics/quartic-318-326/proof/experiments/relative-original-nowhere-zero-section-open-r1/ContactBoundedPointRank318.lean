module
public import ContactBoundedInputRecovery318
public section
noncomputable section
namespace ContactBoundedPointRank318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (f : ContactBoundedPointFamily318.SchemePoint c N b)
local notation "E" => ContactBoundedPointFamily318.extract c N b f
local notation "π" => ContactBoundedSchemeHilbertData318.projection c N b E
lemma rank (x : B) : π.finrank x=(ContactBoundedHilbertParameter318.projection c N).finrank (f.val x) := by
  rw [ClosedFamilyCanonicalProperties318.rank,ContactBoundedPointFamily318.into_base]
  exact ContactBoundedPointFamily318.rank c N b f x
variable (d : Fin (N+1))
local notation "U" => ContactBoundedRankCover318.cover c N b E
local notation "i" => ContactBoundedHilbertParameter318.into c N d
lemma range : Set.range (U.f d ≫ f.val) ⊆ Set.range i := by
  rintro _ ⟨x,rfl⟩
  apply (ContactBoundedHilbertParameter318.rank_iff_component c N d _).mp
  rw [← rank]
  exact ContactBoundedRankCover318.rank c N b E d x
/-- Actual factor through the component determined by the extracted
whole-family rank; this is a scheme morphism, not a pointwise function. -/
@[expose] def factor : U.X d ⟶ ContactBoundedHilbertParameter318.component c N d :=
  IsOpenImmersion.lift i (U.f d ≫ f.val) (range c N b f d)
@[reassoc] lemma factor_into : factor c N b f d ≫ i=U.f d ≫ f.val :=
  IsOpenImmersion.lift_fac _ _ _
@[expose] def point : ContactSchemePointFamily318.SchemePoint c d.val
    (ContactBoundedRankData318.base c N b E d) := ⟨factor c N b f d,by
  rw [← ContactBoundedHilbertParameter318.into_structure c N d,← Category.assoc,
    factor_into,Category.assoc,f.property]
  rfl⟩
end ContactBoundedPointRank318
