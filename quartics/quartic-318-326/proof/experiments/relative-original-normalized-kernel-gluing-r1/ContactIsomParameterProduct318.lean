module
public import ContactPicardDiagonalImageFactorization318
public section
noncomputable section
namespace ContactIsomParameterProduct318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K M N : Line (curve R c))
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c
/-- Product of ANY two of the same original Isom parameters over the
actual coefficient base, including the equal-endpoint torsor square. -/
abbrev parameter := pullback (q L K) (q M N)
@[expose] def base : parameter R c L K M N ⟶ Spec R := pullback.fst (q L K) (q M N) ≫ q L K
@[expose] def first : Points R c L K (base R c L K M N) := ⟨pullback.fst _ _,rfl⟩
@[expose] def second : Points R c M N (base R c L K M N) :=
  ⟨pullback.snd _ _,(pullback.condition).symm⟩
variable {T : Scheme.{0}} (b : T ⟶ Spec R)
@[expose] def pairMap (z : Points R c L K b) (w : Points R c M N b) :
    T ⟶ parameter R c L K M N := pullback.lift z.val w.val (z.property.trans w.property.symm)
lemma pairMap_fst (z : Points R c L K b) (w : Points R c M N b) :
    pairMap R c L K M N b z w ≫ pullback.fst (q L K) (q M N)=z.val :=
  pullback.lift_fst _ _ _
lemma pairMap_snd (z : Points R c L K b) (w : Points R c M N b) :
    pairMap R c L K M N b z w ≫ pullback.snd (q L K) (q M N)=w.val :=
  pullback.lift_snd _ _ _
lemma pairMap_base (z : Points R c L K b) (w : Points R c M N b) :
    pairMap R c L K M N b z w ≫ base R c L K M N=b := by
  rw [base,←Category.assoc,pairMap_fst,z.property]
lemma universal_pair : pairMap R c L K M N (base R c L K M N)
    (first R c L K M N) (second R c L K M N)=𝟙 (parameter R c L K M N) := by
  apply pullback.hom_ext
  · simpa only [Category.id_comp] using pairMap_fst R c L K M N
      (base R c L K M N) (first R c L K M N) (second R c L K M N)
  · simpa only [Category.id_comp] using pairMap_snd R c L K M N
      (base R c L K M N) (first R c L K M N) (second R c L K M N)
end ContactIsomParameterProduct318
