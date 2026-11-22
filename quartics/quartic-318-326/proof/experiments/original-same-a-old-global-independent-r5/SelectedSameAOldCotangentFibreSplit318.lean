module

public import SelectedSameASmoothTransitivitySplit318
import all SelectedSameASmoothTransitivitySplit318
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The original smooth cotangent row on its genuine affine fibre

The actual splitting upstairs survives arbitrary scalar change. The
stock cotangent pushout and its generator formula identify the actual
right arrow; no hypothetical flatness of this fibre map is invoked.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace SelectedSameAOldCotangentFibreSplit318

universe u
noncomputable section

section ExtensionFunctor

variable (C B : Type u) [CommRing C] [CommRing B] [Algebra C B]

/-- Use the actual commutative algebra tensor action, avoiding any
presupposed reconciliation between scalar restriction presentations. -/
@[expose] def actualTensor : ModuleCat.{u} C ⥤ ModuleCat.{u} B where
  obj M := ModuleCat.of B (B ⊗[C] M)
  map f := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor B B f.hom)
  map_id M := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.lTensor_id
  map_comp f g := by
    apply ModuleCat.hom_ext
    exact TensorProduct.AlgebraTensorModule.lTensor_comp (A := B) (M := B) g.hom f.hom

instance actualTensor_additive : (actualTensor C B).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.hom_ext
    exact map_add (TensorProduct.AlgebraTensorModule.lTensor B B) f.hom g.hom

end ExtensionFunctor

open SelectedSameASmoothTransitivitySplit318

variable (k T C B : Type u) [CommRing k] [CommRing T] [CommRing C] [CommRing B]
  [Algebra k T] [Algebra k C] [Algebra T C] [Algebra T k] [Algebra k B]
  [Algebra T B] [Algebra C B] [IsScalarTower k T C] [IsScalarTower T C B]
  [IsScalarTower T k B] [IsScalarTower k C B] [Algebra.IsPushout T k C B]

/-- On the same actual fibre, this is the pullback of the first map,
re-associating the true three scalar extensions. -/
@[expose] def leftOnFibre : B ⊗[T] KaehlerDifferential k T →ₗ[B] B ⊗[C] KaehlerDifferential k C :=
  (TensorProduct.AlgebraTensorModule.lTensor B B (jacobian k T C)).comp
    (TensorProduct.AlgebraTensorModule.cancelBaseChange T C B B (KaehlerDifferential k T)).symm.toLinearMap

/-- Whole-map normalization: the base-changed relative quotient is
the literal differential projection on the true affine fibre. -/
theorem rightOnFibre :
    (KaehlerDifferential.tensorKaehlerEquiv T k C B).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor B B (relativeProjection k T C)) =
    KaehlerDifferential.mapBaseChange k C B := by
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a ω =>
    have hω : ω ∈ Submodule.span C (Set.range (KaehlerDifferential.D k C)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    refine Submodule.span_induction (p := fun v _ => ∀ b : B,
      ((KaehlerDifferential.tensorKaehlerEquiv T k C B).toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.lTensor B B (relativeProjection k T C))) (b ⊗ₜ[C] v) =
      KaehlerDifferential.mapBaseChange k C B (b ⊗ₜ[C] v)) ?_ ?_ ?_ ?_ hω a
    · rintro _ ⟨z, rfl⟩ b
      change KaehlerDifferential.tensorKaehlerEquiv T k C B
        (TensorProduct.AlgebraTensorModule.lTensor B B (relativeProjection k T C)
          (b ⊗ₜ[C] KaehlerDifferential.D k C z)) =
        KaehlerDifferential.mapBaseChange k C B (b ⊗ₜ[C] KaehlerDifferential.D k C z)
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul, KaehlerDifferential.map_D,
        KaehlerDifferential.tensorKaehlerEquiv_tmul_D, KaehlerDifferential.mapBaseChange_tmul,
        KaehlerDifferential.map_D]
    · intro b
      simp
    · intro v w _ _ hv hw b
      rw [TensorProduct.tmul_add, map_add, map_add, hv b, hw b]
    · intro c v _ hv b
      rw [← TensorProduct.smul_tmul]
      exact hv (c • b)

theorem fibre_comp_zero :
    ModuleCat.ofHom (leftOnFibre k T C B) ≫
      ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B) = 0 := by
  let L := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor B B (jacobian k T C))
  let P := ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor B B (relativeProjection k T C))
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange T C B B (KaehlerDifferential k T)).toModuleIso
  let f := (KaehlerDifferential.tensorKaehlerEquiv T k C B).toModuleIso
  have h : L ≫ P = 0 := ((smoothTransitivityRow k T C).map (actualTensor C B)).zero
  calc
    _ = e.inv ≫ (L ≫ P) ≫ f.hom := by
      rw [← rightOnFibre k T C B]
      simp only [leftOnFibre, ModuleCat.ofHom_comp, Category.assoc] <;> rfl
    _ = 0 := by rw [h, Limits.zero_comp, Limits.comp_zero]

/-- The first and last maps are both literally read in the affine fibre,
not unrelated maps under a choice of source basis. -/
@[expose] def oldFibreRow : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.mk (ModuleCat.ofHom (leftOnFibre k T C B))
    (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B))
    (fibre_comp_zero k T C B)

/-- The genuine old row is split on each such affine, even on a ramified
or nonflat special fibre. Flatness of scalar change is not needed. -/
theorem oldFibreRow_split [Algebra.FormallySmooth T C] :
    Nonempty ((oldFibreRow k T C B).Splitting) := by
  obtain ⟨sp⟩ := split_before_reduction k T C
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange T C B B (KaehlerDifferential k T)).toModuleIso
  let f := (KaehlerDifferential.tensorKaehlerEquiv T k C B).toModuleIso
  have iso : ((smoothTransitivityRow k T C).map (actualTensor C B)) ≅ oldFibreRow k T C B := by
    refine ShortComplex.isoMk e (Iso.refl _) f ?_ ?_
    · change e.hom ≫ ModuleCat.ofHom (leftOnFibre k T C B) = _ ≫ 𝟙 _
      have hh : ModuleCat.ofHom (leftOnFibre k T C B) = e.inv ≫
          ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor B B (jacobian k T C)) := rfl
      rw [hh, Iso.hom_inv_id_assoc, Category.comp_id] <;> rfl
    · change 𝟙 _ ≫ ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B) =
        ModuleCat.ofHom (TensorProduct.AlgebraTensorModule.lTensor B B (relativeProjection k T C)) ≫ f.hom
      rw [Category.id_comp, ← ModuleCat.ofHom_comp, rightOnFibre]
  exact ⟨(sp.map (actualTensor C B)).ofIso iso⟩

end

end SelectedSameAOldCotangentFibreSplit318
