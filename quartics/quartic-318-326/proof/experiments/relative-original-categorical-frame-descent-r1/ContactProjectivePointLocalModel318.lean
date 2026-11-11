module
public import ContactProjectivePointFamily318
public section
noncomputable section
namespace ContactProjectivePointLocalModel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (x : ContactProjectiveParameterPoint318.Point c n S) (φ : S →ₐ[ℚ] T) (a : Chart) (I : Ideal c a T n)
  (hI : (ContactProjectiveParameterPoint318.ofIdeal c n T a I).val=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x.val)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "q" => ContactProjectiveUniversalGluing318.original c n
local notation "qi" => projectiveInto c a T n I
local notation "d" => RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ p
local notation "b" => ContactProjectivePointFamily318.sourceMap c n S x
local notation "k" => ContactProjectiveUniversalChartRecovery318.toFamily c n a T I
lemma outer : IsPullback k qi q (d ≫ b) := by
  have h := ContactProjectiveUniversalChartRecovery318.source_cartesian c n a T I
  rw [← OriginalAffineCoefficientIdentity318.map_eq S T φ c,
    RelativeSchemeCoefficient318.comp,← hI]
  exact h
@[expose] def map : family c a T n I ⟶ ContactProjectivePointFamily318.family c n S x :=
  PullbackIntermediateFactor318.lift k qi q d b (outer c n S T x φ a I hI)
    (ContactProjectivePointFamily318.toFamily c n S x) (ContactProjectivePointFamily318.into c n S x)
    (ContactProjectivePointFamily318.cartesian c n S x)
@[reassoc] lemma source : map c n S T x φ a I hI ≫ ContactProjectivePointFamily318.into c n S x=qi ≫ d :=
  PullbackIntermediateFactor318.lift_right _ _ _ _ _ _ _ _ _
lemma cartesian : IsPullback (map c n S T x φ a I hI) qi
    (ContactProjectivePointFamily318.into c n S x) d :=
  PullbackIntermediateFactor318.cartesian _ _ _ _ _ _ _ _ _
end ContactProjectivePointLocalModel318
