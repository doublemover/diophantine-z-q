module

public import CanonicalDifferentialSheafMap318
public import TildeComparison318
public import ScalarExtensionTensor318
public import AffineIntrinsicNormalization318
public import IntrinsicDifferentialPullback318
public import InvariantTransition318

/-!
# Normalize the actual affine Kähler projection under nonflat pullback

There is no étale or flat hypothesis on the true reduction C -> B.
The same canonical affine sheaf map has the actual tensor projection.
-/

public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra

set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace SelectedSameAFibreAffineProjection318

universe u
noncomputable section
variable (k C B : Type u) [CommRing k] [CommRing C] [CommRing B]
  [Algebra k C] [Algebra k B] [Algebra C B] [IsScalarTower k C B]

abbrev r := CommRingCat.ofHom (algebraMap C B)
abbrev M := ModuleCat.of C (KaehlerDifferential k C)
abbrev N := ModuleCat.of B (KaehlerDifferential k B)

/-- The actual affine tensor row's right map, with the precise scalar
extension functor rather than a freely chosen tensor realization. -/
@[expose] noncomputable def rightLinear :
    (ModuleCat.extendScalars (algebraMap C B)).obj (M k C) ⟶ N k B :=
  ModuleCat.ofHom ((KaehlerDifferential.mapBaseChange k C B).comp
    (ScalarExtensionTensor318.tensorEquiv (T := B) (M k C)).toLinearMap)

theorem rightLinear_tmul (b : B) (w : KaehlerDifferential k C) :
    rightLinear k C B (b ⊗ₜ[C, algebraMap C B] w) =
      b • KaehlerDifferential.map k k C B w := by
  change (KaehlerDifferential.mapBaseChange k C B)
    (ScalarExtensionTensor318.tensorEquiv (T := B) (M k C)
      (b ⊗ₜ[C, algebraMap C B] w)) = _
  rw [ScalarExtensionTensor318.tensorEquiv_tmul, KaehlerDifferential.mapBaseChange_tmul]

/-- The actual right map sends 1 tensor ds to d of the actual reduction. -/
theorem rightLinear_D (x : C) :
    rightLinear k C B ((1 : B) ⊗ₜ[C, algebraMap C B] KaehlerDifferential.D k C x) =
      KaehlerDifferential.D k B (algebraMap C B x) := by
  rw [rightLinear_tmul, one_smul, KaehlerDifferential.map_D]

private theorem rightLinear_adjoint :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap C B)).homEquiv _ _ (rightLinear k C B) =
      CanonicalDifferentialSheafMap318.differentialModuleMap (R := k) (S := C) (T := B) := by
  ext w
  change (ModuleCat.extendRestrictScalarsAdj (algebraMap C B)).homEquiv _ _
      (rightLinear k C B) (KaehlerDifferential.D k C w) =
    KaehlerDifferential.map k k C B (KaehlerDifferential.D k C w)
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, rightLinear_tmul, one_smul]

/-- The canonical affine differential map, transposed to the true pullback. -/
@[expose] noncomputable def right :
    (Scheme.Modules.pullback (Spec.map (r C B))).obj
      (CanonicalDifferentialSheafMap318.sourceSheaf (R := k) (S := C)) ⟶
      CanonicalDifferentialSheafMap318.targetSheaf (R := k) (T := B) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (r C B))).homEquiv _ _).symm
    (CanonicalDifferentialSheafMap318.sheafMap (R := k) (S := C) (T := B))

/-- Compare the actual morphisms, not only the source and target objects.
The map is the canonical normalized affine pullback followed by tilde of
the literal tensor projection. -/
theorem right_normalized :
    right k C B =
      (TildePullback318.pullbackIso (r C B)).hom.app (M k C) ≫
        (tilde.functor (CommRingCat.of B)).map (rightLinear k C B) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map (r C B))).homEquiv _ _).injective
  unfold right
  rw [Equiv.apply_symm_apply]
  apply ((tilde.adjunction (R := CommRingCat.of C)).homEquiv _ _).injective
  rw [CanonicalDifferentialSheafMap318.adjoint_sheafMap]
  apply (cancel_mono (PushforwardGlobalSections318.globalIso (r C B)
    (CanonicalDifferentialSheafMap318.targetSheaf (R := k) (T := B))).hom).mp
  have hh := TildeComparison318.global_composite (r C B) (M k C) (N k B)
      (rightLinear k C B)
  simp only [CommRingCat.hom_ofHom] at hh
  rw [rightLinear_adjoint k C B] at hh
  simpa only [CanonicalDifferentialSheafMap318.pushedSheaf,
    CanonicalDifferentialSheafMap318.targetSheaf,
    CanonicalDifferentialSheafMap318.sourceSheaf, CanonicalDifferentialSheafMap318.baseMap,
    AffineDifferentialSheaf318.differentialSheaf, tilde.functor, CommRingCat.hom_ofHom,
    CanonicalDifferentialSheafMap318.moduleToGlobal, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using hh.symm

/-- The same comparison, now targeting tilde of the honest algebra tensor
module rather than the restricted-scalar presentation. -/
@[expose] noncomputable def tensorIso :
    (Scheme.Modules.pullback (Spec.map (r C B))).obj
      (CanonicalDifferentialSheafMap318.sourceSheaf (R := k) (S := C)) ≅
    tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C)) :=
  (TildePullback318.pullbackIso (r C B)).app (M k C) ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (ScalarExtensionTensor318.tensorEquiv (T := B) (M k C)).toModuleIso

theorem right_on_tensor :
    right k C B =
      (tensorIso k C B).hom ≫ (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B)) := by
  rw [right_normalized]
  simp only [tensorIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
    ← Functor.map_comp] <;> rfl

abbrev chart (T : Type u) [CommRing T] := Spec (CommRingCat.of T)
abbrev overK (T : Type u) [CommRing T] [Algebra k T] :
    chart T ⟶ chart k := Spec.map (CommRingCat.ofHom (algebraMap k T))

/-- The genuine affines' base triangle follows from the scalar tower. -/
theorem over_comp : Spec.map (r C B) ≫ overK k C = overK k B := by
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  intro s
  exact (IsScalarTower.algebraMap_apply k C B s).symm

/-- Intrinsic affine differentials and algebraic differential tilde maps
have the same right arrow, not merely isomorphic endpoints. -/
theorem affine_intrinsic_right :
    (Scheme.Modules.pullback (Spec.map (r C B))).map
        (AffineIntrinsicNormalization318.algebraIso (R := k) (S := C)).hom ≫
      IntrinsicDifferentialPullback318.pullbackMap (Spec.map (r C B))
        (overK k B) (overK k C) (over_comp k C B) =
    right k C B ≫ (AffineIntrinsicNormalization318.algebraIso (R := k) (S := B)).hom := by
  let f := Spec.map (r C B)
  let ic := (AffineIntrinsicNormalization318.algebraIso (R := k) (S := C)).hom
  let ib := (AffineIntrinsicNormalization318.algebraIso (R := k) (S := B)).hom
  let pd := IntrinsicDifferentialPullback318.map f (overK k B) (overK k C) (over_comp k C B)
  let cs := CanonicalDifferentialSheafMap318.sheafMap (R := k) (S := C) (T := B)
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    IntrinsicDifferentialPullback318.pullbackMap_adjoint]
  unfold right
  rw [Equiv.apply_symm_apply]
  change ic ≫ pd = cs ≫ (Scheme.Modules.pushforward f).map ib
  apply ((tilde.adjunction (R := CommRingCat.of C)).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  let m := (tilde.isoTop (R := CommRingCat.of C) (M k C)).hom
  change m ≫ moduleSpecΓFunctor.map (ic ≫ pd) =
    m ≫ moduleSpecΓFunctor.map (cs ≫ (Scheme.Modules.pushforward f).map ib)
  have he : (m ≫ moduleSpecΓFunctor.map (ic ≫ pd)).hom.toAddMonoidHom =
      (m ≫ moduleSpecΓFunctor.map (cs ≫ (Scheme.Modules.pushforward f).map ib)).hom.toAddMonoidHom := by
    apply KaehlerAdditiveExt318.ext
    · intro x
      have hb := CanonicalDifferentialSheafMap318.global_image_D (R := k) (S := C) (T := B) x
      rw [InvariantTransition318.globalIso_apply] at hb
      change pd.val.app (op ⊤) ((moduleSpecΓFunctor.map ic) (m (KaehlerDifferential.D k C x))) =
        (moduleSpecΓFunctor.map ib) ((moduleSpecΓFunctor.map cs) (m (KaehlerDifferential.D k C x)))
      rw [AffineIntrinsicNormalization318.algebra_D, IntrinsicDifferentialPullback318.map_D,
        hb, AffineIntrinsicNormalization318.algebra_D]
      have hΓ := congrArg (fun g => g x) (Scheme.ΓSpecIso_inv_naturality (r C B))
      exact congrArg ((FamilyIntrinsicDifferentials318.D (overK k B)).d) hΓ.symm
    · intro x w hw
      change (m ≫ moduleSpecΓFunctor.map (ic ≫ pd)) (x • w) =
        (m ≫ moduleSpecΓFunctor.map (cs ≫ (Scheme.Modules.pushforward f).map ib)) (x • w)
      rw [map_smul, map_smul]
      exact congrArg (fun v => x • v) hw
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro w
  exact DFunLike.congr_fun he w

end SelectedSameAFibreAffineProjection318
