module
public import ContactAvoidanceAffineWholeFamily318
public import AffineWholeFamilyClassification318
public import AffineWholeFamilyNaturality318
public section
noncomputable section
namespace ContactFixedDegreeLocalClassifier318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactProjectiveDegreeData318
open scoped TensorProduct
variable (S : CommRingCat.{0}) [Algebra ℚ S] (c : Fin 4 → ℚˣ) (n : ℕ)
  (D : FixedDegree S c n)
@[expose] def bounded : BoundedDegree S c n := ⟨D.val,fun x => (D.property x).le⟩
abbrev cover := ContactBoundedAvoidanceAffineCover318.cover S c n (bounded S c n D)
abbrev index := (cover S c n D).I₀
variable (a : index S c n D)
local notation "Db" => bounded S c n D
local notation "T" => ContactBoundedAvoidanceAffineCover318.ring S c n Db a
local notation "A" => ContactAvoidanceAffineWholeFamily318.sourceRing S c n Db a
local notation "f" => ContactAvoidanceAffineWholeFamily318.affineInto S c n Db a
local notation "π" => ContactAvoidanceAffineWholeFamily318.projection S c n Db a
local notation "i" => ContactProjectiveQuotientGluing318.into S c D.val.datum
local notation "p" => ContactProjectiveQuotientGluing318.projection S c D.val.datum
local instance finite : IsFinite (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change IsFinite (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactAvoidanceAffineWholeFamily318.affine_projection]; infer_instance
local instance flat : Flat (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change Flat (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactAvoidanceAffineWholeFamily318.affine_projection]; infer_instance
local instance presentation : LocallyOfFinitePresentation (AffineWholeQuotientProjection318.projection ℚ A T f) := by
  change LocallyOfFinitePresentation (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T)
  rw [ContactAvoidanceAffineWholeFamily318.affine_projection]; infer_instance
lemma rank (x : PrimeSpectrum T) :
    (AffineWholeQuotientProjection318.projection ℚ A T f).finrank x=Fintype.card (Fin n) := by
  change (f ≫ VaryingSourceCoefficientPullback318.projection ℚ A T).finrank x=_
  rw [ContactAvoidanceAffineWholeFamily318.affine_projection]
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (ContactAvoidanceAffineWholeFamily318.cartesian S c n Db a)]
  rw [FiniteAffineRankComparison318.rank_eq]
  simpa only [Fintype.card_fin] using D.property _
/-- Every original effective finite-flat constant-degree Cartier divisor
is locally an ACTUAL point of the finite-projective affine quotient
parameter scheme, on a proved WHOLE coefficient cover. -/
@[expose] def point : VaryingParameterPoint318.Point ℚ A (Fin n) T :=
  AffineWholeFamilyClassification318.point ℚ A T (Fin n) f (rank S c n D a)
/-- The local classifier recovers the entire original restricted family,
including its original closed embedding and coefficient projection. -/
@[expose] def comparison : ContactAvoidanceAffineWholeFamily318.family S c n Db a ≅
    VaryingParameterPointFamily318.family ℚ A (Fin n) T (point S c n D a) :=
  AffineWholeFamilyClassification318.familyComparison ℚ A T (Fin n) f (rank S c n D a)
@[reassoc] lemma comparison_into : (comparison S c n D a).hom ≫
    VaryingParameterPointFamily318.intoSource ℚ A (Fin n) T (point S c n D a)=f :=
  AffineWholeFamilyClassification318.comparison_into ℚ A T (Fin n) f (rank S c n D a)
@[reassoc] lemma comparison_projection : (comparison S c n D a).hom ≫
    VaryingParameterPointFamily318.projection ℚ A (Fin n) T (point S c n D a)=π :=
  (AffineWholeFamilyClassification318.comparison_projection ℚ A T (Fin n) f (rank S c n D a)).trans
    (ContactAvoidanceAffineWholeFamily318.affine_projection S c n Db a)
lemma recovered_ideal : VaryingParameterPointIdeal318.ideal ℚ A (Fin n) T (point S c n D a)=
    AffineClosedQuotientExtraction318.ideal (T ⊗[ℚ] A) f :=
  AffineWholeFamilyClassification318.recovered_ideal ℚ A T (Fin n) f (rank S c n D a)
end ContactFixedDegreeLocalClassifier318
