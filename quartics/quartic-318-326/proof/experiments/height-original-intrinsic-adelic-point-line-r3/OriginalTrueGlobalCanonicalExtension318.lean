module
public import OriginalTrueGlobalZoomComparison318
public import OriginalIntegralBranchPointComparison318
public section
noncomputable section
namespace OriginalTrueGlobalCanonicalExtension318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPrimeIntegralBicanonical318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
  {m : OriginalAllPrimeZoomInput318.Mode} (I : OriginalAllPrimeZoomInput318.Input c t w D m)
  (i : Fin 4)

/-- Actual canonical integral extension of the genuine global q0, using
the balanced map on the ENTIRE differential tensor square of the SAME
constructed smooth integral neighborhood. -/
theorem section0 : ContactTrueGlobalTensorPullback318.image c i
    (originalBranchMap c t w D I i) (ContactGlobalBicanonical318.q0 c) =
    BaseChangingDifferentialTensor318.tensorMap (S:=K c t)
      (IntegralContactZoomBaseChange318.coefficientMap (S:=K c t)
        D.coefficients (contacts c t w) I.coordinate (mode m))
      (integralSection0 c t w D I) := by
  rw [ContactTrueGlobalTensorPullback318.image_q0]
  exact (original_q0 c t w D I i).symm.trans
    (IntegralContactZoomTensorBaseChange318.tensorMap_section0 _ _ _ _).symm

theorem section1 : ContactTrueGlobalTensorPullback318.image c i
    (originalBranchMap c t w D I i) (ContactGlobalBicanonical318.q1 c) =
    BaseChangingDifferentialTensor318.tensorMap (S:=K c t)
      (IntegralContactZoomBaseChange318.coefficientMap (S:=K c t)
        D.coefficients (contacts c t w) I.coordinate (mode m))
      (integralSection1 c t w D I) := by
  rw [ContactTrueGlobalTensorPullback318.image_q1]
  exact (original_q1 c t w D I i).symm.trans
    (IntegralContactZoomTensorBaseChange318.tensorMap_section1 _ _ _ _).symm

variable (hn : ∀ j,RationalContactPoint318.parameters c t j≠0)
include hn in
/-- Equality of full morphisms into the ACTUAL proper smooth Q-curve,
not merely the normalized arithmetic candidate or a point tuple. -/
theorem original_point :
    Spec.map (CommRingCat.ofHom (OriginalIntegralBranchPointComparison318.evaluation c t w D I).toRingHom) ≫
      ContactTrueGlobalTensorPullback318.schemeMap c i (originalBranchMap c t w D I i) =
        RationalContactPoint318.point c t := by
  calc
    _ = Spec.map (CommRingCat.ofHom
        ((OriginalIntegralBranchPointComparison318.evaluation c t w D I).toRingHom.comp
          (originalBranchMap c t w D I i).toRingHom)) ≫
        ContactIntrinsicFrames318.branchEmbedding c i := by
      rw [ContactTrueGlobalTensorPullback318.schemeMap,←Category.assoc,←Spec.map_comp]
      rfl
    _ = Spec.map (CommRingCat.ofHom (ContactBranchPoint318.branchPoint c t hn i)) ≫
        ContactIntrinsicFrames318.branchEmbedding c i := by
      rw [OriginalIntegralBranchPointComparison318.whole_original_branch_point c t hn w D I i]
    _ = _ := ContactBranchPoint318.branchMap_original c t hn i

include hn in
/-- Every original noncontact point at EVERY finite place has produced
smooth integral neighborhoods whose genuine canonical tensor sections
pull back BOTH actual global bicanonical sections and whose whole generic
point is the original proper-Q-curve point. This does not identify these
neighborhood lattices with a global regular-model/Hodge lattice. -/
theorem exists_extension : ∃ (D : Data c t w) (m : OriginalAllPrimeZoomInput318.Mode)
    (I : OriginalAllPrimeZoomInput318.Input c t w D m),
    Algebra.Smooth (V c t w) I.Chart ∧
    ∀ i : Fin 4,
      ContactTrueGlobalTensorPullback318.image c i (originalBranchMap c t w D I i)
        (ContactGlobalBicanonical318.q0 c) =
        BaseChangingDifferentialTensor318.tensorMap (S:=K c t)
          (IntegralContactZoomBaseChange318.coefficientMap (S:=K c t)
            D.coefficients (contacts c t w) I.coordinate (mode m)) (integralSection0 c t w D I) ∧
      ContactTrueGlobalTensorPullback318.image c i (originalBranchMap c t w D I i)
        (ContactGlobalBicanonical318.q1 c) =
        BaseChangingDifferentialTensor318.tensorMap (S:=K c t)
          (IntegralContactZoomBaseChange318.coefficientMap (S:=K c t)
            D.coefficients (contacts c t w) I.coordinate (mode m)) (integralSection1 c t w D I) ∧
      Spec.map (CommRingCat.ofHom (OriginalIntegralBranchPointComparison318.evaluation c t w D I).toRingHom) ≫
        ContactTrueGlobalTensorPullback318.schemeMap c i (originalBranchMap c t w D I i) =
          RationalContactPoint318.point c t := by
  obtain ⟨D,g,hbase,hpoint⟩ := OriginalAllPlaceNormalizedData318.exists_center c t w
  obtain ⟨m,⟨I⟩⟩ := OriginalAllPrimeZoomInput318.exists_input c t w D hn
  exact ⟨D,m,I,I.smooth,fun i => ⟨section0 c t w D I i,section1 c t w D I i,
    original_point c t w D I i hn⟩⟩
end OriginalTrueGlobalCanonicalExtension318
