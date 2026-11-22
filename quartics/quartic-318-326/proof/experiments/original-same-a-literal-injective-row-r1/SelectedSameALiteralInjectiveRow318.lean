module

public import SelectedSameAGenuineBoundaryLifts318
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Injective presentation of the two original contracted boundaries

The application sets `S = G.map oldDirect`, `L = G(O_A)` and
`λ = G.map L_A` on the literal additive opens site of the same fibre.
The left leg of the comparison is precisely the input λ. No directional
row, new exactness assumption, or general Čech comparison is used.
-/

public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

namespace SelectedSameALiteralInjectiveRow318

universe u w

variable (X : TopCat.{u})

/-- The small site of actual opens has enough injectives in the literal
category used by the original degree-zero boundary. -/
theorem actual_enough_injectives :
    EnoughInjectives (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
  letI : IsGrothendieckAbelian.{u}
      (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) := inferInstance
  exact IsGrothendieckAbelian.enoughInjectives.{u}

/-- One may choose the small-site universe for the actual Ext boundary,
without installing a new global instance for all callers. -/
theorem actual_hasExt :
    HasExt.{u} (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) := by
  letI := actual_enough_injectives X
  exact hasExt_of_enoughInjectives
    (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})

local instance siteEnoughInjectives :
    EnoughInjectives (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  actual_enough_injectives X

/-- The stock monomorphism of the same target sheaf, followed by its
actual cokernel projection. -/
@[expose] noncomputable def target
    (L : Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    ShortComplex (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  ShortComplex.cokernelSequence (Injective.ι L)

theorem target_shortExact
    (L : Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    (target X L).ShortExact := by
  refine ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact (Injective.ι L)) ?_ ?_
  · change Mono (Injective.ι L)
    infer_instance
  · change Epi (cokernel.π (Injective.ι L))
    infer_instance

variable {S : ShortComplex (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})}
variable {L : Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u}}

/-- Extend the chosen left leg along the actual mono of the old row,
then descend its projection along the actual cokernel of that mono. -/
noncomputable def factor (hOld : S.ShortExact) (lambdaA : S.X₁ ⟶ L) :
    S ⟶ target X L := by
  letI : Mono S.f := hOld.mono_f
  let s : S.X₂ ⟶ Injective.under L := Injective.factorThru (lambdaA ≫ Injective.ι L) S.f
  have hs : S.f ≫ s = lambdaA ≫ Injective.ι L :=
    Injective.comp_factorThru (lambdaA ≫ Injective.ι L) S.f
  have hz : S.f ≫ (s ≫ cokernel.π (Injective.ι L)) = 0 := by
    rw [← Category.assoc, hs, Category.assoc, cokernel.condition, comp_zero]
  let v := CokernelCofork.IsColimit.desc' hOld.gIsCokernel
    (s ≫ cokernel.π (Injective.ι L)) hz
  have hv : S.g ≫ v.val = s ≫ cokernel.π (Injective.ι L) := v.property
  exact { τ₁ := lambdaA, τ₂ := s, τ₃ := v.val, comm₁₂ := hs.symm, comm₂₃ := hv.symm }

theorem factor_left (hOld : S.ShortExact) (lambdaA : S.X₁ ⟶ L) :
    (factor X hOld lambdaA).τ₁ = lambdaA := by
  unfold factor
  rfl

/-- Literal contracted old class equals the boundary of its image in the
one chosen injective presentation. Applies to each of the two original
ordered top sections and preserves the same Ext universe/convention. -/
theorem boundary_eq
    [HasExt.{w} (Sheaf (_root_.Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (hOld : S.ShortExact) (lambdaA : S.X₁ ⟶ L)
    (z : S.X₃.obj.obj (op (⊤ : TopologicalSpace.Opens X))) :
    SelectedSameAGenuineBoundaryLifts318.boundary X (target_shortExact X L)
        ((factor X hOld lambdaA).τ₃.hom.app (op (⊤ : TopologicalSpace.Opens X)) z) =
      Sheaf.H.map lambdaA 1 (SelectedSameAGenuineBoundaryLifts318.boundary X hOld z) := by
  simpa only [factor_left] using
    SelectedSameAGenuineBoundaryLifts318.boundary_natural
      X hOld (target_shortExact X L) (factor X hOld lambdaA) z

end SelectedSameALiteralInjectiveRow318
