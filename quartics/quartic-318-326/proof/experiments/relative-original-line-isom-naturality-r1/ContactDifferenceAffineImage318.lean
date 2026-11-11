module
public import LocalImageCoverDescent318
public section
noncomputable section
namespace ContactDifferenceAffineImage318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ContactOriginalRelativePolynomialCharts318
variable (c : Fin 4 → ℚˣ) (R : CommRingCat.{0}) [Algebra ℚ R]
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
/-- The internally constructed common fppf parameter proves the actual
image sieve is covering for every original affine naive class. -/
lemma covering (x : RelativeLineClassBaseChange318.TestClass p (baseMap R)) :
    Presheaf.imageSieve (ContactCartierDifferenceAbel318.transformation c)
      (RelativeClassSheafPoint318.value p (baseMap R) x) ∈
        RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ)) (Over.mk (baseMap R)) := by
  obtain ⟨T,t,hf,hs,hp,N,M,D,E,he⟩ := ContactAffineRelativeClassPresentation318.exists_presentation R c x
  letI := hf
  letI := hs
  letI := hp
  apply FppfSingleCover318.sieve_mem (baseMap R) (t ≫ baseMap R) t rfl
  exact ⟨(⟨N,D⟩,⟨M,E⟩),he⟩
end ContactDifferenceAffineImage318
