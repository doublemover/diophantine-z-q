module
public import ContactBoundedRankCover318
public section
noncomputable section
namespace ContactBoundedRankData318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
  (D : ContactBoundedSchemeHilbertData318.Data c N b) (d : Fin (N+1))
local notation "i" => ContactBoundedRankCover318.into c N b D d
abbrev base := i ≫ b
abbrev bounded := ContactBoundedHilbertBaseChange318.map c N b (base c N b D d) i rfl D
/-- Every derived rank component is standard fixed-rank data on its
ENTIRE coefficient scheme, with the same full restricted ideal. -/
@[expose] def data : ContactSchemeHilbertData318.Data c d.val (base c N b D d) where
  ideal := (bounded c N b D d).ideal
  finite := inferInstance
  flat := inferInstance
  presentation := inferInstance
  rank x := by
    rw [ContactBoundedHilbertBaseChange318.rank]
    exact ContactBoundedRankCover318.rank c N b D d x
abbrev point := ContactSchemeHilbertEquiv318.equivalence c d.val (base c N b D d) (data c N b D d)
abbrev map : (ContactBoundedRankCover318.locus c N b D d).toScheme ⟶ ContactBoundedHilbertParameter318.scheme c N :=
  (point c N b D d).val ≫ ContactBoundedHilbertParameter318.into c N d
@[reassoc] lemma over : map c N b D d ≫ ContactBoundedHilbertParameter318.structureMap c N=i ≫ b := by
  rw [map,Category.assoc,ContactBoundedHilbertParameter318.into_structure]
  exact (point c N b D d).property
end ContactBoundedRankData318
