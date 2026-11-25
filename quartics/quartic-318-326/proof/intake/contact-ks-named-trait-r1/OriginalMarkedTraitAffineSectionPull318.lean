module
public import OriginalRetainedComplexZeroByPasting318
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
Evaluate the exact old two affine coefficients through the actual prolonged
marked trait. The generic read is produced by the same Scheme arrow.
It is a hom on the displayed localization, never on the curve function field.
-/

@[expose] public section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits
open OriginalRetainedComplexZeroByPasting318 (specOf spec_comp)

namespace OriginalMarkedTraitAffineSectionPull318

universe u
variable {V E : Type u} [CommRing V] [IsLocalRing V] [Field E]
variable {Y : Scheme.{u}} (U : Y.Opens) (hU : IsAffineOpen U)
variable (t : Spec (.of V) ⟶ Y)
variable (closed : t (IsLocalRing.closedPoint V) ∈ U)

abbrev chartRing := Γ(Y, U)

include closed in
theorem whole_trait : t ⁻¹ᵁ U = ⊤ :=
  Scheme.preimage_eq_top_of_closedPoint_mem t closed

include closed in
theorem range_on_chart : Set.range t ⊆ Set.range hU.fromSpec := by
  rw [hU.range_fromSpec]
  rintro _ ⟨x, rfl⟩
  change x ∈ t ⁻¹ᵁ U
  rw [whole_trait U t closed]
  exact Set.mem_univ _

/-- The actual trait factors through THIS chart because it contains the
closed point; no second trait or reduction-compatible map is chosen. -/
def into_chart : Spec (.of V) ⟶ Spec (Γ(Y, U)) :=
  IsOpenImmersion.lift hU.fromSpec t (range_on_chart U hU t closed)

@[reassoc] theorem into_chart_over :
    into_chart U hU t closed ≫ hU.fromSpec = t :=
  IsOpenImmersion.lift_fac _ _ _

def evalHom : Γ(Y, U) ⟶ CommRingCat.of V :=
  Spec.preimage (into_chart U hU t closed)

def eval : chartRing U →+* V := (evalHom U hU t closed).hom

private theorem spec_eval :
    specOf (eval U hU t closed) = into_chart U hU t closed := by
  unfold specOf eval
  rw [CommRingCat.ofHom_hom]
  exact Spec.map_preimage (into_chart U hU t closed)

theorem eval_on_exact_model :
    specOf (eval U hU t closed) ≫ hU.fromSpec = t := by
  rw [spec_eval]
  exact into_chart_over U hU t closed

variable (tau : V →+* E) (x : Spec (.of E) ⟶ Y)
variable (is_old_mark : specOf tau ≫ t = x)

/-- Evaluate in the SAME retained E, retaining the entire actual fine mark. -/
def genericEval : chartRing U →+* E := tau.comp (eval U hU t closed)

include is_old_mark in
theorem realizes_old_mark :
    specOf (genericEval U hU t closed tau) ≫ hU.fromSpec = x := by
  unfold genericEval
  rw [← spec_comp, Category.assoc, eval_on_exact_model, is_old_mark]

include is_old_mark in
theorem genericEval_unique (g : chartRing U →+* E)
    (hg : specOf g ≫ hU.fromSpec = x) :
    g = genericEval U hU t closed tau := by
  have h : specOf g = specOf (genericEval U hU t closed tau) :=
    (cancel_mono hU.fromSpec).mp (hg.trans
      (realizes_old_mark U hU t closed tau x is_old_mark).symm)
  exact congrArg CommRingCat.Hom.hom (Spec.map_inj.mp h)

variable (π : chartRing U)
variable (unit_in_E : IsUnit (genericEval U hU t closed tau π))

/-- The exact original affine localization on which the former R4 section
formula lives. No map out of a whole function field is inferred. -/
def liftEval : Localization.Away π →+* E :=
  IsLocalization.Away.lift π (g := genericEval U hU t closed tau) unit_in_E

theorem liftEval_read (a : chartRing U) :
    liftEval U hU t closed tau π unit_in_E (algebraMap (chartRing U) (Localization.Away π) a) =
      tau (eval U hU t closed a) :=
  IsLocalization.Away.lift_eq π unit_in_E a

/-- Former R4 yields exactly these unique affine coefficients. Here their
actual images in the marked trait are **constructed** and their generic
read at the same mark is proved. -/
theorem pull_section_pair (generic : Fin 2 → Localization.Away π)
    (oldIntegral : ∀ i, ∃! a : chartRing U,
      algebraMap (chartRing U) (Localization.Away π) a = generic i) :
    ∃ z : Fin 2 → V,
      (∀ i, z i = eval U hU t closed (oldIntegral i).choose) ∧
      (∀ i, tau (z i) = liftEval U hU t closed tau π unit_in_E (generic i)) := by
  refine ⟨fun i => eval U hU t closed (oldIntegral i).choose, fun _ => rfl, fun i => ?_⟩
  have hi := (oldIntegral i).choose_spec.1
  rw [← hi, liftEval_read]

end OriginalMarkedTraitAffineSectionPull318

#print axioms OriginalMarkedTraitAffineSectionPull318.eval_on_exact_model
#print axioms OriginalMarkedTraitAffineSectionPull318.realizes_old_mark
#print axioms OriginalMarkedTraitAffineSectionPull318.genericEval_unique
#print axioms OriginalMarkedTraitAffineSectionPull318.pull_section_pair
