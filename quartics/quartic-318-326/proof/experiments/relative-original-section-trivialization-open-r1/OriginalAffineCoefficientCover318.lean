module
public import FppfSingleCover318
public section
noncomputable section
namespace OriginalAffineCoefficientCover318
open AlgebraicGeometry CategoryTheory
variable {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
abbrev cover (_b : B ⟶ Spec (CommRingCat.of ℚ)) := B.affineOpenCover
abbrev index := (cover b).I₀
abbrev ring (i : index b) : CommRingCat.{0} := (cover b).X i
@[expose] instance algebra (i : index b) : Algebra ℚ (ring b i) :=
  (Spec.preimage ((cover b).f i ≫ b)).hom.toAlgebra
lemma base (i : index b) : ContactOriginalRelativePolynomialCharts318.baseMap (ring b i)=(cover b).f i ≫ b :=
  Spec.map_preimage _
@[expose] def object (i : index b) : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk (ContactOriginalRelativePolynomialCharts318.baseMap (ring b i))
@[expose] def arrow (i : index b) : object b i ⟶ Over.mk b := Over.homMk ((cover b).f i) (base b i).symm
/-- Every original base scheme is covered by actual affine coefficient
rings with their literal induced rational algebra structures. -/
lemma covering : Sieve.ofArrows (object b) (arrow b) ∈
    RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ)) (Over.mk b) := by
  rw [RelativeFppfLineSheaf318.topology,GrothendieckTopology.mem_over_iff,Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  apply (Scheme.ofArrows_mem_precoverage_iff (P:=@Flat ⊓ @LocallyOfFinitePresentation)).mpr
  constructor
  · intro x
    exact ⟨(cover b).idx x,(cover b).covers x⟩
  · intro i
    exact ⟨inferInstance,inferInstance⟩
end OriginalAffineCoefficientCover318
