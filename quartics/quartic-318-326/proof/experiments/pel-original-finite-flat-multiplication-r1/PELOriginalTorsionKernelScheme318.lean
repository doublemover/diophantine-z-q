module
public import PELOriginalTranslationAutomorphisms318
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public section
noncomputable section
namespace PELOriginalTorsionKernelScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemeAdditionOperations318 PELOriginalSchemePointGroup318
open PELOriginalSchemeGroupUnitInverse318 PELOriginalIntegerMultiplication318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)

/-- The actual scheme-theoretic kernel. Nilpotents and infinitesimal
structure are retained by the categorical equalizer, not discarded by a
complex-point zero locus or reduced closed subscheme. -/
abbrev kernel : Scheme := equalizer (multiplication τ hτ n) (constantZero τ hτ)
abbrev inclusion : kernel τ hτ n ⟶ candidate τ hτ :=
  equalizer.ι (multiplication τ hτ n) (constantZero τ hτ)
@[expose] def structureMap : kernel τ hτ n ⟶ Spec (CommRingCat.of ℂ) :=
  inclusion τ hτ n≫π τ hτ

/-- The n-torsion subgroup on any actual complex test scheme. -/
def torsion {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ)) :
    AddSubgroup (Points τ hτ Y ρ) where
  carrier := {p | n • p=0}
  zero_mem' := zsmul_zero n
  add_mem' := by intro p q hp hq; rw [zsmul_add,hp,hq,add_zero]
  neg_mem' := by intro p hp; rw [zsmul_neg,hp,neg_zero]

lemma torsion_iff {Y : Scheme} {ρ : Y ⟶ Spec (CommRingCat.of ℂ)}
    (p : Points τ hτ Y ρ) :
    n • p=0 ↔ p.val≫multiplication τ hτ n=p.val≫constantZero τ hτ := by
  constructor
  · intro h
    rw [test_action τ hτ n p.val p.property,constant_zero τ hτ ρ p]
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    rw [←test_action τ hτ n p.val p.property]
    exact h.trans (constant_zero τ hτ ρ p)

abbrev KernelPoints (Y : Scheme) (ρ : Y ⟶ Spec (CommRingCat.of ℂ)) :=
  {p : Y ⟶ kernel τ hτ n // p≫structureMap τ hτ n=ρ}

/-- Both-inverse representation of the entire torsion subgroup functor,
valid for ALL test schemes. This is a scheme-theoretic kernel statement,
not merely a computation of complex-valued torsion points. -/
@[expose] def pointsEquiv {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ)) :
    KernelPoints τ hτ n Y ρ ≃ torsion τ hτ n ρ where
  toFun p := ⟨⟨p.val≫inclusion τ hτ n,by
      rw [Category.assoc]; exact p.property⟩,
    (torsion_iff τ hτ n _).mpr (by
      simp only [Category.assoc,inclusion,equalizer.condition])⟩
  invFun p := ⟨equalizer.lift p.val.val ((torsion_iff τ hτ n p.val).mp p.property),by
    rw [structureMap,←Category.assoc,equalizer.lift_ι]
    exact p.val.property⟩
  left_inv p := by
    apply Subtype.ext
    apply equalizer.hom_ext
    exact equalizer.lift_ι _ _
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact equalizer.lift_ι _ _

/-- The representing equivalence retains the literal ambient point. -/
lemma pointsEquiv_inclusion {Y : Scheme} (ρ : Y ⟶ Spec (CommRingCat.of ℂ))
    (p : KernelPoints τ hτ n Y ρ) :
    (pointsEquiv τ hτ n ρ p).val.val=p.val≫inclusion τ hτ n := rfl
end PELOriginalTorsionKernelScheme318
