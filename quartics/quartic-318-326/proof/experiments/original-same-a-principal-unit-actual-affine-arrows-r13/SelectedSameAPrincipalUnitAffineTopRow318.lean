module

public import SelectedSameAPrincipalUnitActualAffineArrows318
public import SelectedSameAActualAffineAmbientTop318
public import SelectedSameAPrincipalUnitBoundary318
public import SelectedSameAPrincipalUnitMiddleChart318

/-!
Normalize the actual section arrows on Spec B, then transfer the
split coefficient row back through the tilde counit of the same
restricted sheaves. No short exactness assumption on the original
reduction complex enters the affine result.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SelectedSameAPrincipalUnitAffineTopRow318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open SelectedSameAActualAffineAmbientTop318 (Γj topAdd topAdd_smul topAdd_map)
open SelectedSameAActualAffineOpenCoefficientIso318 (coordinateIso coordinateIso_hom)
open SelectedSameAPrincipalUnitActualAffineArrows318
open SelectedSameAActualConstantAffineCoefficients318 (actualCoordinateIso)
open SelectedSameAPrincipalUnitPushforwardArrows318 (projection middle unit V left)
open SelectedSameAPrincipalUnitActualReduction318 (coor readReduction)
open SelectedSameAConstantPrincipalLine318 (constantScheme constantCocycle markedEpsilon markedEpsilon_sq)
open SelectedSameAActualNilpotentLineGluing318 (AdditiveCocycle unitCocycle)

variable {k : Type u} [Field k] {A : Scheme.{u}}
variable (a : A ⟶ Spec (CommRingCat.of k))
variable {B : Type u} [CommRing B] [Algebra k B]
variable (j : Spec (CommRingCat.of B) ⟶ A) [IsOpenImmersion j]
variable (hj : j ≫ a = SelectedSameAConstantTargetTriangle318.sp (algebraMap k B))

abbrev T := TrivSqZeroExt B B

theorem coordinate_inverse (b : B) :
    baseCoordinate j ((coordinateIso j (W j) rfl).inv b) = b := by
  change SelectedSameAActualAffineOpenCoefficientIso318.coordinate j (W j) rfl
    ((coordinateIso j (W j) rfl).inv b) = b
  rw [← coordinateIso_hom]
  exact Iso.inv_hom_id_apply (C := CommRingCat) (coordinateIso j (W j) rfl)
    (show CommRingCat.of B from b)

/-- Both ends use the actual reduced structural coordinate of the selected
affine Spec; this is not the top of an independently chosen sheaf. -/
@[expose] def ends :
    (Γj (B := B)).obj ((unit A : A.Modules).restrict j) ≃ₗ[B] B := by
  let N : ModuleCat B := (Γj (B := B)).obj ((unit A : A.Modules).restrict j)
  let e := coordinateIso j (W j) rfl
  let t := topAdd j (unit A)
  let F : (N : Type u) →ₗ[B] B :=
    { toFun := fun z : N => baseCoordinate j (t.hom z)
      map_add' := by intro x y; simp only [map_add]
      map_smul' := by
        intro b z
        change baseCoordinate j (t.hom (show N from b • z)) =
          b * baseCoordinate j (t.hom z)
        rw [topAdd_smul j (unit A) b z]
        change baseCoordinate j (e.inv b * t.hom z) = _
        change SelectedSameAActualAffineOpenCoefficientIso318.coordinate j (W j) rfl
          (e.inv b * t.hom z) = _
        rw [map_mul]
        exact congrArg (fun w : B => w * baseCoordinate j (t.hom z)) (coordinate_inverse j b) }
  exact LinearEquiv.ofBijective F ((ConcreteCategory.bijective_of_isIso e.hom).comp
    (ConcreteCategory.bijective_of_isIso t.hom))

variable {I : Type u} (U : I → A.Opens) (c : AdditiveCocycle U)
variable (hc : (⊤ : A.Opens) ≤ ⨆ i, U i)
variable (M : (constantScheme a).Modules)
variable (f : ∀ i, unit ((V a U i).toScheme) ≅ M.restrict (V a U i).ι)
variable (hframe : LineFrameCocycle318.cocycle M (V a U) f =
  unitCocycle (V a U) (markedEpsilon a) (markedEpsilon_sq a) (constantCocycle a U c))
variable (i : I) (hW : W j ≤ U i)

/-- The middle top uses the actual given frame on the original open,
its actual closed thickening, and the actual scalar chart map. -/
@[expose] def middleTop :
    (Γj (B := B)).obj ((middle a M).restrict j) ≃ₗ[B] T (B := B) := by
  let N : ModuleCat B := (Γj (B := B)).obj ((middle a M).restrict j)
  let t := topAdd j (middle a M)
  let E := coor a U M f i (W j) hW
  let e := coordinateIso j (W j) rfl
  let F : (N : Type u) →ₗ[B] T (B := B) :=
    { toFun := fun z : N => coefficient a j hj U M f i hW (t.hom z)
      map_add' := by
        intro x y
        simp only [coefficient, dualCoordinate, map_add]
      map_smul' := by
        intro b z
        change coefficient a j hj U M f i hW (t.hom (show N from b • z)) =
          b • coefficient a j hj U M f i hW (t.hom z)
        have he : t.hom (show N from b • z) = e.inv b • t.hom z :=
          topAdd_smul j (middle a M) b z
        rw [he]
        change dualCoordinate a j hj (E.symm (((projection a).app (W j) (e.inv b)) •
          (show Γ(M,WD a j) from t.hom z))) = b • _
        rw [LinearEquiv.map_smul, smul_eq_mul]
        change (actualCoordinateIso a j hj).hom
          (((projection a).app (W j) (e.inv b)) * E.symm (t.hom z)) = _
        rw [map_mul]
        change dualCoordinate a j hj ((projection a).app (W j) (e.inv b)) *
          coefficient a j hj U M f i hW (t.hom z) = _
        rw [constant_beta a j hj, coordinate_inverse j b]
        exact (Algebra.smul_def b _).symm }
  exact LinearEquiv.ofBijective F
    ((ConcreteCategory.bijective_of_isIso (actualCoordinateIso a j hj).hom).comp
      (E.symm.bijective.comp (ConcreteCategory.bijective_of_isIso t.hom)))

/-- Γ of the actual left arrow in the actual chart, with the original
epsilon sign and no unproved beta condition. -/
theorem left_top (z : (Γj (B := B)).obj ((unit A : A.Modules).restrict j)) :
    middleTop a j hj U M f i hW ((Γj (B := B)).map ((Scheme.Modules.restrictFunctor j).map
      (left a U c hc M f hframe)) z) =
        TrivSqZeroExt.inr (ends j z) := by
  change coefficient a j hj U M f i hW
      ((topAdd j (middle a M)).hom ((Γj (B := B)).map ((Scheme.Modules.restrictFunctor j).map
        (left a U c hc M f hframe)) z)) =
    TrivSqZeroExt.inr (baseCoordinate j ((topAdd j (unit A)).hom z))
  rw [topAdd_map]
  exact left_inr a j hj U c hc M f hframe i hW ((topAdd j (unit A)).hom z)

include c hc hframe in
/-- Γ of the actual right arrow reads the reduction in the same chart
coordinates used for the left arrow. -/
theorem right_top (z : (Γj (B := B)).obj ((middle a M).restrict j)) :
    ends j ((Γj (B := B)).map ((Scheme.Modules.restrictFunctor j).map
      (readReduction a U c M f hframe hc)) z) =
        (middleTop a j hj U M f i hW z).fst := by
  change baseCoordinate j
      ((topAdd j (unit A)).hom ((Γj (B := B)).map ((Scheme.Modules.restrictFunctor j).map
        (readReduction a U c M f hframe hc)) z)) =
    (coefficient a j hj U M f i hW ((topAdd j (middle a M)).hom z)).fst
  rw [topAdd_map]
  exact right_fst a j hj U c hc M f hframe i hW ((topAdd j (middle a M)).hom z)

private instance globalSectionsPreservesZero :
    (Γj (B := B)).PreservesZeroMorphisms := by
  constructor
  intro M N
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

private instance tildePreservesZero :
    (tilde.functor (CommRingCat.of B)).PreservesZeroMorphisms := by
  letI : (tilde.functor (CommRingCat.of B)).Additive := by
    constructor
    intro M N g h
    exact AlgebraicGeometry.tilde.map_add g h
  exact Functor.preservesZeroMorphisms_of_additive (tilde.functor (CommRingCat.of B))

variable (jD : Spec (CommRingCat.of (T (B := B))) ⟶ constantScheme a)
variable [IsOpenImmersion jD]
variable (H : IsPullback (SelectedSameAPrincipalUnitMiddleChart318.q B) jD j (projection a))
include f hW H in
/-- The frame in the affine preimage is the actual restriction of the
one already used for the two arrow formulas, via its genuine open map. -/
@[expose] def affineLineFrame :
    unit (Spec (CommRingCat.of (T (B := B)))) ≅ M.restrict jD := by
  have hr : Set.range jD ⊆ Set.range (V a U i).ι := by
    rintro _ ⟨z, rfl⟩
    have hx : j (SelectedSameAPrincipalUnitMiddleChart318.q B z) ∈ W j :=
      Scheme.Hom.mem_opensRange.mpr ⟨_, rfl⟩
    have h := congrArg (fun g => g z) H.w
    change j (SelectedSameAPrincipalUnitMiddleChart318.q B z) = projection a (jD z) at h
    refine ⟨⟨jD z, ?_⟩, rfl⟩
    change projection a (jD z) ∈ U i
    rw [← h]
    exact hW hx
  let l := IsOpenImmersion.lift (V a U i).ι jD hr
  have hl : l ≫ (V a U i).ι = jD := IsOpenImmersion.lift_fac _ _ _
  letI : IsOpenImmersion (l ≫ (V a U i).ι) := by rw [hl]; infer_instance
  letI : IsOpenImmersion l := IsOpenImmersion.of_comp l (V a U i).ι
  exact (Scheme.Modules.restrictUnitIso l).symm ≪≫
    (Scheme.Modules.restrictFunctor l).mapIso (f i) ≪≫
    ((Scheme.Modules.restrictFunctorComp l (V a U i).ι).symm.app M) ≪≫
    ((Scheme.Modules.restrictFunctorCongr hl).app M)

abbrev restricted :=
  (SelectedSameAPrincipalUnitBoundary318.row a U c hc M f hframe).map
    (Scheme.Modules.restrictFunctor j)

include hj hW H in
/-- For the same actual affine preimage and its genuine line frame, the
whole restricted short complex splits. Use the natural affine tilde
counit of the three actual modules to transport the literal Γ splitting. -/
theorem affine_split :
    Nonempty ((restricted a j U c hc M f hframe).Splitting) := by
  let S := restricted a j U c hc M f hframe
  let G := Γj (B := B)
  let L := tilde.functor (CommRingCat.of B)
  letI : G.PreservesZeroMorphisms := globalSectionsPreservesZero
  letI : L.PreservesZeroMorphisms := tildePreservesZero
  let D := SelectedSameAPrincipalUnitAffineReduction318.row B
  let e₀ := (ends j).toModuleIso
  let e₁ := (middleTop a j hj U M f i hW).toModuleIso
  let E : S.map G ≅ D := by
    refine ShortComplex.isoMk e₀ e₁ e₀ ?_ ?_
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (left_top a j hj U c hc M f hframe i hW z).symm
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      exact (right_top a j hj U (c := c) (hc := hc) M f (hframe := hframe) i hW z).symm
  have hE : IsIso ((unit A : A.Modules).restrict j).fromTildeΓ :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf ≪≫ (Scheme.Modules.restrictUnitIso j).symm⟩⟩
  have hM : IsIso ((middle a M).restrict j).fromTildeΓ :=
    SelectedSameAPrincipalUnitMiddleChart318.actual_fromTilde_isIso
      (projection a) B j jD H M (affineLineFrame a j U M f i hW jD H)
  letI : IsIso S.X₁.fromTildeΓ := hE
  letI : IsIso S.X₂.fromTildeΓ := hM
  letI : IsIso S.X₃.fromTildeΓ := hE
  let counit := Scheme.Modules.fromTildeΓNatTrans (R := CommRingCat.of B)
  let e : (S.map G).map L ≅ S := by
    refine ShortComplex.isoMk (asIso S.X₁.fromTildeΓ) (asIso S.X₂.fromTildeΓ)
      (asIso S.X₃.fromTildeΓ) ?_ ?_
    · exact (counit.naturality S.f).symm
    · exact (counit.naturality S.g).symm
  let s := (SelectedSameAPrincipalUnitAffineReduction318.splitting B).ofIso E.symm
  exact ⟨(s.map L).ofIso e⟩

end SelectedSameAPrincipalUnitAffineTopRow318
