module
public import VaryingParameterPointFamily318
public section
noncomputable section
namespace VaryingPointFamilyBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable (R A ι S : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] [CommRing S] [Algebra R S]
variable (x : VaryingParameterPoint318.Point R A ι S)
variable (T : Type u) [CommRing T] [Algebra R T] (f : S →ₐ[R] T)
local notation "xT" => VaryingParameterPoint318.map R A ι S T f x
local notation "pS" => VaryingParameterPointFamily318.projection R A ι S x
local notation "pT" => VaryingParameterPointFamily318.projection R A ι T xT
local notation "iS" => VaryingParameterPointFamily318.intoFamily R A ι S x
local notation "iT" => VaryingParameterPointFamily318.intoFamily R A ι T xT
local notation "qS" => VaryingParameterPointFamily318.intoSource R A ι S x
local notation "qT" => VaryingParameterPointFamily318.intoSource R A ι T xT
local notation "π" => VaryingWordGlobalFamilyProjection318.projection R A ι
local notation "c" => VaryingSourceCoefficientPullback318.coefficientChange R S T f
@[expose] def map : VaryingParameterPointFamily318.family R A ι T xT ⟶
    VaryingParameterPointFamily318.family R A ι S x :=
  pullback.lift iT (pT ≫ c) (by
    rw [Category.assoc]
    exact pullback.condition)
@[reassoc] lemma map_family : map R A ι S x T f ≫ iS=iT := pullback.lift_fst _ _ _
@[reassoc] lemma map_projection : map R A ι S x T f ≫ pS=pT ≫ c := pullback.lift_snd _ _ _
lemma cartesian : IsPullback (map R A ι S x T f) pT pS c := by
  apply IsPullback.of_right (h₁₂ := iS) (h₂₂ := x.val)
  · simpa only [map_family] using (IsPullback.of_hasPullback π xT.val).flip
  · exact map_projection R A ι S x T f
  · exact (IsPullback.of_hasPullback π x.val).flip
@[reassoc] lemma map_source : map R A ι S x T f ≫ qS=
    qT ≫ VaryingSourceCoefficientPullback318.sourceChange R A S T f := by
  apply (VaryingSourceCoefficientPullback318.tensor_cartesian R A S).hom_ext
  · simp only [Category.assoc,VaryingParameterPointFamily318.into_projection,
      VaryingSourceCoefficientPullback318.source_projection,← Category.assoc]
    exact map_projection R A ι S x T f
  · simp only [Category.assoc,VaryingParameterPointFamily318.into_original,
      VaryingSourceCoefficientPullback318.source_original,← Category.assoc,map_family]
lemma source_cartesian : IsPullback (map R A ι S x T f) qT qS
    (VaryingSourceCoefficientPullback318.sourceChange R A S T f) := by
  apply IsPullback.of_bot (v₂₁ := VaryingSourceCoefficientPullback318.projection R A T)
    (v₂₂ := VaryingSourceCoefficientPullback318.projection R A S)
  · simpa only [VaryingParameterPointFamily318.into_projection] using cartesian R A ι S x T f
  · exact map_source R A ι S x T f
  · exact VaryingSourceCoefficientPullback318.cartesian R A S T f
end VaryingPointFamilyBaseChange318
