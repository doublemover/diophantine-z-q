module
public import ReducedSchemePointFactorization318
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public section
noncomputable section
namespace ReducedComplexPointMorphisms318
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme} (π : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType π]

/-- A closed target condition verified at EVERY genuine C-valued point
holds on the entire source scheme. Jacobson closed-point density is
used, rather than treating all scheme primes as complex-valued points. -/
theorem range_subset (f : X ⟶ Y) (Z : Closeds Y)
    (h : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p≫π=𝟙 _ →
      (f (p (IsLocalRing.closedPoint ℂ))) ∈ Z) : Set.range f ⊆ Z := by
  letI := LocallyOfFiniteType.jacobsonSpace π
  rintro _ ⟨x,rfl⟩
  by_contra hx
  let U : Set X := f ⁻¹' (Z : Set Y)ᶜ
  have hU : IsOpen U := Z.isClosed.isOpen_compl.preimage f.continuous
  have hn : U.Nonempty := ⟨x,hx⟩
  obtain ⟨y,hy,hyc⟩ := nonempty_inter_closedPoints hn hU.isLocallyClosed
  have he := h (pointOfClosedPoint π y hyc) (pointOfClosedPoint_comp π y hyc)
  rw [pointOfClosedPoint_apply] at he
  exact hy he

/-- Full factorization through the SAME reduced closed subscheme. The
source reducedness and quasi-compact morphism hypotheses are explicit
because pointwise vanishing alone would not kill nilpotents. -/
@[expose] def factor [IsReduced X] (f : X ⟶ Y) [QuasiCompact f] (Z : Closeds Y)
    (h : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p≫π=𝟙 _ →
      f (p (IsLocalRing.closedPoint ℂ)) ∈ Z) :
    X ⟶ (Scheme.IdealSheafData.vanishingIdeal Z).subscheme :=
  ReducedSchemePointFactorization318.factor f Z (range_subset π f Z h)

@[reassoc] theorem factor_inclusion [IsReduced X] (f : X ⟶ Y) [QuasiCompact f]
    (Z : Closeds Y)
    (h : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p≫π=𝟙 _ →
      f (p (IsLocalRing.closedPoint ℂ)) ∈ Z) :
    factor π f Z h ≫ (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι=f :=
  ReducedSchemePointFactorization318.factor_inclusion f Z (range_subset π f Z h)

/-- Genuine equality of scheme morphisms over C from equality on all
C-valued morphisms. This is the exact reduced finite-type/separated
interface used to glue actual regular projective maps. -/
theorem ext [IsReduced X] (σ : Y ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType σ] [IsSeparated σ] (f g : X ⟶ Y)
    (hf : f≫σ=π) (hg : g≫σ=π)
    (h : ∀ p : Spec (CommRingCat.of ℂ) ⟶ X, p≫π=𝟙 _ → p≫f=p≫g) : f=g := by
  letI : LocallyOfFiniteType (f≫σ) := by rw [hf]; infer_instance
  apply AlgebraicGeometry.ext_of_apply_eq σ Set.univ isOpen_univ.isLocallyClosed dense_univ
    _ (hf.trans hg.symm)
  intro x hx hxc
  have he := h (pointOfClosedPoint π x hxc) (pointOfClosedPoint_comp π x hxc)
  have hv := congrArg (fun k : Spec (CommRingCat.of ℂ) ⟶ Y =>
    k (IsLocalRing.closedPoint ℂ)) he
  simpa only [Scheme.Hom.comp_apply,pointOfClosedPoint_apply] using hv
end ReducedComplexPointMorphisms318
