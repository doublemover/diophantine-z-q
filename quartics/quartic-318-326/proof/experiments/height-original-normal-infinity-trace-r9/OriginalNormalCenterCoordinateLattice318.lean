module
public import OriginalNormalCenterCommonChart318
public section
noncomputable section
namespace OriginalNormalCenterCoordinateLattice318
open NumberField
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open OriginalAllPlaceNormalModel318 OriginalNormalCenterCommonChart318
open scoped TensorProduct
set_option maxHeartbeats 1000000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
abbrev Cotangent := OriginalNormalCenterAffineChart318.Cotangent c t w D M
abbrev GenericCotangent := OriginalNormalCenterAffineChart318.GenericCotangent c t w D M

/-- A CONSTRUCTED frame on the previous actual integral-center generic
cotangent, obtained through its genuine common affine chart with the source.
There is no center-frame or dimension-one premise. -/
@[expose] def frame : GenericCotangent c t w D M ≃ₗ[K c t] K c t :=
  genericComparison c t w D M ≪≫ₗ OriginalNormalSourceCotangent318.frame c t w D M

/-- The exact original source dt pulled into the center's generic module. -/
@[expose] def dt : GenericCotangent c t w D M :=
  (genericComparison c t w D M).symm (OriginalNormalSourceCotangent318.dt c t w D M)

theorem frame_dt : frame c t w D M (dt c t w D M) = 1 := by
  rw [frame,dt,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
    OriginalNormalSourceCotangent318.frame_dt]

/-- The ACTUAL original integral cotangent specialization, mapped to the
normalized-source generic cotangent. Torsion is allowed and no integral
generator or membership of dt is assumed. -/
@[expose] def sourceCoordinateMap : Cotangent c t w D M →ₗ[V c t w]
    OriginalNormalSourceCotangent318.Fiber c t w D M :=
  ((genericComparison c t w D M).toLinearMap.restrictScalars (V c t w)).comp
    (AffineSectionCotangentImage318.toGeneric (centerChart c t w D M) (K c t))
@[expose] def sourceLattice : Submodule (V c t w)
    (OriginalNormalSourceCotangent318.Fiber c t w D M) :=
  (sourceCoordinateMap c t w D M).range

/-- Its literal coefficient image in the SAME original point field. -/
@[expose] def coordinateMap : Cotangent c t w D M →ₗ[V c t w] K c t :=
  ((frame c t w D M).toLinearMap.restrictScalars (V c t w)).comp
    (AffineSectionCotangentImage318.toGeneric (centerChart c t w D M) (K c t))
@[expose] def scalarLattice : Submodule (V c t w) (K c t) :=
  (coordinateMap c t w D M).range

theorem coordinateMap_through_source : coordinateMap c t w D M =
    ((OriginalNormalSourceCotangent318.frame c t w D M).toLinearMap.restrictScalars (V c t w)).comp
      (sourceCoordinateMap c t w D M) := by
  ext x
  rfl

theorem frame_tmul (a : K c t) (x : Cotangent c t w D M) :
    frame c t w D M (a ⊗ₜ[V c t w] x) = a * coordinateMap c t w D M x := by
  change frame c t w D M (a ⊗ₜ[V c t w] x) =
    a * frame c t w D M ((1:K c t) ⊗ₜ[V c t w] x)
  have h : a ⊗ₜ[V c t w] x = a • ((1:K c t) ⊗ₜ[V c t w] x) := by
    rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  rw [h,map_smul,smul_eq_mul]

/-- The actual coefficient lattice spans the full original generic line,
including at all bad places. This does NOT say it is the unit lattice. -/
theorem scalar_spans : Submodule.span (K c t) (Set.range (coordinateMap c t w D M)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨x,rfl⟩ := (frame c t w D M).surjective z
  induction x using TensorProduct.induction_on with
  | zero => simpa only [map_zero] using
      (Submodule.zero_mem (Submodule.span (K c t) (Set.range (coordinateMap c t w D M))))
  | tmul a x =>
    rw [frame_tmul]
    exact (Submodule.span (K c t) (Set.range (coordinateMap c t w D M))).smul_mem a
      (Submodule.subset_span ⟨x,rfl⟩)
  | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

theorem scalarLattice_ne_bot : scalarLattice c t w D M ≠ ⊥ := by
  intro h
  have hz : Submodule.span (K c t) (Set.range (coordinateMap c t w D M)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have hx : coordinateMap c t w D M x ∈ scalarLattice c t w D M := ⟨x,rfl⟩
    rw [h] at hx
    simpa only [Submodule.mem_bot] using hx
  rw [scalar_spans] at hz
  have hh : (1:K c t) ∈ (⊥ : Submodule (K c t) (K c t)) := hz trivial
  exact one_ne_zero (Submodule.mem_bot.mp hh)

instance finite_scalarLattice : Module.Finite (V c t w) (scalarLattice c t w D M) := by
  apply Module.Finite.of_surjective (coordinateMap c t w D M).rangeRestrict
  intro x
  obtain ⟨y,hy⟩ := x.property
  exact ⟨y,Subtype.ext hy⟩

/-- A nonzero finite free integral coefficient lattice has now been
constructed from the whole original center. No regularity, Hodge or
relative-dualizing identification is encoded by this freeness assertion. -/
theorem scalarLattice_free : Module.Free (V c t w) (scalarLattice c t w D M) := by
  letI : Module.IsTorsionFree (V c t w) (K c t) := inferInstance
  letI : Module.IsTorsionFree (V c t w) (scalarLattice c t w D M) := inferInstance
  exact Module.free_of_finite_type_torsion_free'
end OriginalNormalCenterCoordinateLattice318
