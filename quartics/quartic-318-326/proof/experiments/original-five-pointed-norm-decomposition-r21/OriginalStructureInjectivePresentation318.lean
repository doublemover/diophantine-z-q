module
public import OriginalHOneRelativeHom318
public section
noncomputable section
namespace OriginalStructureInjectivePresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite LocalSheafCohomologySections318 LocalSheafCohomologyAdditive318
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (X : Scheme.{0})
abbrev O := StructureAdditiveSheaf318.sheaf X
abbrev I := Injective.under (O X)
abbrev inclusion : O X ⟶ I X := Injective.ι (O X)
abbrev Q := cokernel (inclusion X)
abbrev projection : I X ⟶ Q X := cokernel.π (inclusion X)
@[expose] def sequence : ShortComplex (AffineOpenSectionLifting318.ASheaf X) :=
  ShortComplex.mk (inclusion X) (projection X) (cokernel.condition (inclusion X))
lemma shortExact : (sequence X).ShortExact :=
  { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (inclusion X)) }
/-- The actual coefficient connecting map, with its covariant Ext sign. -/
@[expose] def localBoundary (U : X.Opens) :
    (Q X).obj.obj (op U) →+ (O X).H' 1 U :=
  ((shortExact X).extClass.postcomp (generator U) (show 0 + 1 = 1 from rfl)).comp
    (zeroAddEquiv (Q X) U).symm.toAddMonoidHom
lemma localBoundary_surjective (U : X.Opens) : Function.Surjective (localBoundary X U) := by
  intro z
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ (generator U) (shortExact X) z
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  refine ⟨zeroAddEquiv (Q X) U y, ?_⟩
  change ((zeroAddEquiv (Q X) U).symm (zeroAddEquiv (Q X) U y)).comp
    (shortExact X).extClass rfl = z
  rw [AddEquiv.symm_apply_apply]
  exact hy
lemma localBoundary_zero_iff (U : X.Opens) (t : (Q X).obj.obj (op U)) :
    localBoundary X U t = 0 ↔ ∃ a : (I X).obj.obj (op U), (projection X).hom.app (op U) a = t := by
  constructor
  · intro ht
    obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (generator U) (shortExact X)
      ((zeroAddEquiv (Q X) U).symm t) (n₁ := 1) rfl ht
    refine ⟨zeroAddEquiv (I X) U a, ?_⟩
    have he := congrArg (zeroEquiv (Q X) U) ha
    rw [zeroEquiv_naturality] at he
    exact he.trans ((zeroAddEquiv (Q X) U).apply_symm_apply t)
  · rintro ⟨a,rfl⟩
    let z := (zeroAddEquiv (I X) U).symm a
    have hz : z.comp (Ext.mk₀ (projection X)) (add_zero 0) =
        (zeroAddEquiv (Q X) U).symm ((projection X).hom.app (op U) a) := by
      apply (zeroAddEquiv (Q X) U).injective
      change zeroEquiv (Q X) U _ = _
      rw [zeroEquiv_naturality]
      simp only [z, AddEquiv.apply_symm_apply]
    change ((zeroAddEquiv (Q X) U).symm _).comp (shortExact X).extClass rfl = 0
    rw [← hz, Ext.comp_assoc_of_second_deg_zero, (shortExact X).comp_extClass, Ext.comp_zero]
/-- Original global H1 represented without choosing ANY open cover. -/
@[expose] def boundary : (Q X).obj.obj (op ⊤) →+ SheafCohomologyRetraction318.structureH X 1 :=
  (TerminalLocalCohomology318.equivalence X (O X) 1).toAddMonoidHom.comp (localBoundary X ⊤)
lemma boundary_surjective : Function.Surjective (boundary X) :=
  (TerminalLocalCohomology318.equivalence X (O X) 1).surjective.comp (localBoundary_surjective X ⊤)
lemma boundary_zero_iff (t : (Q X).obj.obj (op ⊤)) :
    boundary X t = 0 ↔ ∃ a : (I X).obj.obj (op ⊤), (projection X).hom.app (op ⊤) a = t := by
  change TerminalLocalCohomology318.equivalence X (O X) 1 (localBoundary X ⊤ t) = 0 ↔ _
  constructor
  · intro ht
    apply (localBoundary_zero_iff X ⊤ t).1
    apply (TerminalLocalCohomology318.equivalence X (O X) 1).injective
    simpa only [map_zero] using ht
  · intro ht
    rw [(localBoundary_zero_iff X ⊤ t).2 ht, map_zero]
lemma kernel_eq_range : (boundary X).ker = ((projection X).hom.app (op ⊤)).hom.range := by
  ext t
  exact boundary_zero_iff X t
@[expose] def equivalence :
    (Q X).obj.obj (op ⊤) ⧸ ((projection X).hom.app (op ⊤)).hom.range ≃+
      SheafCohomologyRetraction318.structureH X 1 :=
  (QuotientAddGroup.quotientAddEquivOfEq (kernel_eq_range X).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (boundary X) (boundary_surjective X))
lemma equivalence_mk (t : (Q X).obj.obj (op ⊤)) :
    equivalence X (QuotientAddGroup.mk t) = boundary X t := rfl
/-- Existing affine lifting supplies every actual local lift, including empty
opens, with no replacement of the original structure sheaf kernel. -/
lemma affine_lift [IsIntegral X] (U : X.Opens) (hU : IsAffineOpen U)
    (t : (Q X).obj.obj (op U)) :
    ∃ a : (I X).obj.obj (op U), (projection X).hom.app (op U) a = t :=
  AffineOpenSectionLifting318.surjective_affine_all (sequence X) (shortExact X) (Iso.refl _) U hU t
end OriginalStructureInjectivePresentation318
