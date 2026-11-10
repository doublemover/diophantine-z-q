module
public import OriginalGenericStalkNaturality318
public import OriginalFiniteDeckGalois318
public section
noncomputable section
namespace OriginalSchemeDeckFieldAction318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
variable {G F : Type} [Group G] [Finite G] [Field F]
  {X B : Scheme} [IsIntegral X] [IsIntegral B]
  (p : X ⟶ B) [IsDominant p] [IsSeparated p]
  (κ : F →+* B.functionField)
  (b : G → (X ≅ X))
  (bone : (b 1).hom = 𝟙 X)
  (bmul : ∀ v w, (b (v*w)).hom = (b v).hom ≫ (b w).hom)
  (hover : ∀ w, (b w).hom ≫ p = p)

/-- The original base algebra is the literal composite of the specified
quotient coordinate with the actual generic-stalk pullback of p. -/
@[expose] def baseAlgebra : Algebra F X.functionField :=
  ((DominantFunctionField318.map p).hom.comp κ).toAlgebra

/-- The ORIGINAL scheme automorphism's generic-stalk isomorphism. -/
@[expose] def ringEquiv (w : G) : X.functionField ≃+* X.functionField :=
  OpenFunctionField318.fieldEquiv (b w).hom

lemma ringEquiv_hom (w : G) : (ringEquiv b w).toRingHom =
    (DominantFunctionField318.map (b w).hom).hom := rfl

include hover in
lemma fixes_base (w : G) (r : F) :
    ringEquiv b w ((DominantFunctionField318.map p).hom (κ r)) =
      (DominantFunctionField318.map p).hom (κ r) := by
  have h := DominantFunctionField318.map_comp (b w).hom p
  rw [hover w] at h
  have he := ConcreteCategory.congr_hom h (κ r)
  exact he.symm

include hover in
/-- No separately supplied field representation: each automorphism is the
literal pullback of the OLD whole-curve map. -/
@[expose] def algEquiv (w : G) : letI := baseAlgebra p κ;
    X.functionField ≃ₐ[F] X.functionField := by
  letI := baseAlgebra p κ
  exact { ringEquiv b w with commutes' := fixes_base p κ b hover w }

include bone bmul hover in
/-- The scheme-composition convention is explicit: b(vw)=b(v) then b(w).
Contravariant pullback consequently gives the literal field homomorphism,
without an unrecorded inverse or opposite-group switch. -/
@[expose] def representation : letI := baseAlgebra p κ;
    G →* (X.functionField ≃ₐ[F] X.functionField) := by
  letI := baseAlgebra p κ
  refine { toFun := algEquiv p κ b hover, map_one' := ?_, map_mul' := ?_ }
  · apply AlgEquiv.ext
    intro x
    have h := OriginalGenericStalkNaturality318.map_id (X := X)
    rw [← bone] at h
    exact ConcreteCategory.congr_hom h x
  · intro v w
    apply AlgEquiv.ext
    intro x
    have h := DominantFunctionField318.map_comp (b v).hom (b w).hom
    rw [← bmul v w] at h
    exact ConcreteCategory.congr_hom h x

include bone bmul hover in
/-- Faithfulness of the ORIGINAL whole-curve maps implies faithfulness on
its SAME generic stalk via the actual separated schematic-density theorem. -/
theorem representation_injective (hb : Function.Injective (fun w => (b w).hom)) :
    letI := baseAlgebra p κ;
    Function.Injective (representation p κ b bone bmul hover) := by
  letI := baseAlgebra p κ
  intro v w h
  apply hb
  apply OriginalGenericStalkNaturality318.maps_equal p (b v).hom (b w).hom
    ((hover v).trans (hover w).symm)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact AlgEquiv.congr_fun h x

include bone bmul hover in
lemma representation_apply (w : G) (x : X.functionField) :
    letI := baseAlgebra p κ;
    representation p κ b bone bmul hover w x =
      (DominantFunctionField318.map (b w).hom).hom x := rfl

include bone bmul hover in
/-- The generic square used by the reconstruction endpoint is now proved
for the literal generic-stalk morphism and the constructed field action. -/
theorem generic_square (w : G) :
    letI := baseAlgebra p κ;
    OriginalGenericStalkNaturality318.generic X ≫ (b w).hom =
      Spec.map (CommRingCat.ofHom (representation p κ b bone bmul hover w).toRingHom) ≫
        OriginalGenericStalkNaturality318.generic X := by
  letI := baseAlgebra p κ
  exact OriginalGenericStalkNaturality318.naturality (b w).hom

include bone bmul hover in
/-- An actual faithful whole-curve deck action with the actual quotient
fixed-function identity gives the SAME generic stalk a finite Galois
structure. No separately supplied faithful field representation remains. -/
theorem field_structure (hb : Function.Injective (fun w => (b w).hom))
    (hfixed : ∀ x : X.functionField, (∀ w, ringEquiv b w x = x) →
      ∃ r : F, (DominantFunctionField318.map p).hom (κ r) = x) :
    letI := baseAlgebra p κ;
    FiniteDimensional F X.functionField ∧ IsGalois F X.functionField ∧
      Module.finrank F X.functionField = Nat.card G := by
  letI := baseAlgebra p κ
  let ρ := representation p κ b bone bmul hover
  have hf : Function.Injective ρ := representation_injective p κ b bone bmul hover hb
  have hfix : ∀ x : X.functionField, (∀ w, ρ w x = x) →
      ∃ r : F, algebraMap F X.functionField r = x := hfixed
  exact ⟨OriginalFiniteDeckGalois318.finiteDimensional ρ hf hfix,
    OriginalFiniteDeckGalois318.isGalois ρ hf hfix,
    OriginalFiniteDeckGalois318.finrank ρ hf hfix⟩
end OriginalSchemeDeckFieldAction318
