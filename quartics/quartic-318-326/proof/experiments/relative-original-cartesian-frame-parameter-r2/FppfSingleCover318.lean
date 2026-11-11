module
public import ContactAffineRelativeClassPresentation318
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public section
noncomputable section
namespace FppfSingleCover318
open AlgebraicGeometry CategoryTheory
variable {S B T : Scheme.{0}} (b : B ⟶ S) (t : T ⟶ S) (f : T ⟶ B) (hf : f ≫ b=t)
  [hflat : Flat f] [hsurj : Surjective f] [hfp : LocallyOfFinitePresentation f]
include hflat hsurj hfp in
/-- A genuine flat surjective locally finitely presented scheme map is
one covering arrow in the ACTUAL big relative fppf topology. -/
lemma covering : Sieve.ofArrows (fun _ : PUnit => Over.mk t) (fun _ => Over.homMk f hf) ∈
    RelativeFppfLineSheaf318.topology S (Over.mk b) := by
  rw [RelativeFppfLineSheaf318.topology,GrothendieckTopology.mem_over_iff,Sieve.overEquiv_ofArrows]
  apply Precoverage.generate_mem_toGrothendieck
  apply (Scheme.ofArrows_mem_precoverage_iff (P:=@Flat ⊓ @LocallyOfFinitePresentation)).mpr
  constructor
  · intro x
    obtain ⟨y,hy⟩ := f.surjective x
    exact ⟨PUnit.unit,y,hy⟩
  · intro i
    exact ⟨inferInstance,inferInstance⟩
include hflat hsurj hfp in
lemma sieve_mem (V : Sieve (Over.mk b)) (h : V (Over.homMk f hf)) :
    V ∈ RelativeFppfLineSheaf318.topology S (Over.mk b) := by
  apply (RelativeFppfLineSheaf318.topology S).superset_covering _ (covering b t f hf)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact h
end FppfSingleCover318
