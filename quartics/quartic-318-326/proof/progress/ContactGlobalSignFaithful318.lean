module
public import ContactGlobalSignAction318
public import SourceSignFieldComparison318
public section
noncomputable section
namespace ContactGlobalSignFaithful318
open AlgebraicGeometry CategoryTheory ContactKummerOrder318
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
variable (c : Fin 4 → ℚˣ)
abbrev L := SourceFractionField318.L c
local instance : Field (L c) := (KummerTensorField318.source_raw_field c).toField
local instance : Algebra (SourceOrder c) (L c) := (embedding c).toAlgebra
local instance : IsFractionRing (SourceOrder c) (L c) := SourceFractionField318.actual_fractionField c

/-- Equality of the actual whole-Scheme maps detects the original Boolean signs. -/
theorem injective : Function.Injective (ContactGlobalSigns318.map c) := by
  letI := ContactProjectiveModel318.sourceOpen_open c
  intro s t h
  have ho : ContactGlobalSigns318.openMap c s = ContactGlobalSigns318.openMap c t := by
    apply (cancel_mono (ContactProjectiveModel318.sourceOpen c)).mp
    rw [←ContactGlobalSigns318.on_open, ←ContactGlobalSigns318.on_open, h]
  have he : ∀ x : OpenOrder c, ContactGlobalSigns318.openEquiv c s x =
      ContactGlobalSigns318.openEquiv c t x := by
    intro x
    exact congrArg (fun f => f.hom x) (Spec.map_injective ho)
  have hf : (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) s).toRingHom =
      (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) t).toRingHom := by
    apply IsFractionRing.ringHom_ext (A := SourceOrder c)
    intro x
    change FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) s (embedding c x) =
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) t (embedding c x)
    rw [←SourceOpenFractionField318.openEmbedding_on_order]
    rw [←SourceSignFieldComparison318.open_embedding, ←SourceSignFieldComparison318.open_embedding, he]
  apply FourRootAutomorphisms318.signEquiv_injective (SourceKummerField318.parameter c)
  ext x
  exact RingHom.congr_fun hf x

theorem iso_injective : Function.Injective (ContactGlobalSigns318.iso c) := by
  intro s t h
  exact injective c (congrArg (fun e => e.hom) h)

/-- Exactly sixteen members in this actual sign-action image, not a claim
that the source has no other automorphisms. -/
theorem image_card : Nat.card (Set.range (ContactGlobalSigns318.map c)) = 16 := by
  rw [←Nat.card_congr (Equiv.ofInjective _ (injective c))]
  simp
end ContactGlobalSignFaithful318
