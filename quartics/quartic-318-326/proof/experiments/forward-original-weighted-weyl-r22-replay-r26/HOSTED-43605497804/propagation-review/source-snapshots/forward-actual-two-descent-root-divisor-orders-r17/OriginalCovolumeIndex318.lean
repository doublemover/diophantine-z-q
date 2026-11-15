module
public import OriginalAttainedMinima318
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public section
noncomputable section
namespace OriginalCovolumeIndex318
open MeasureTheory
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalFullEuclideanLattice318 OriginalIntegerSquaredNorm318
set_option maxHeartbeats 3000000

/-- The fixed unit-covolume reference is the STANDARD orthonormal integer
lattice, not a lattice obtained from the non-unimodular quartic coordinates. -/
@[expose] def standardModule : Submodule ℤ E :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)

@[expose] def integerModule : Submodule ℤ E where
  carrier := embedHom.range
  zero_mem' := embedHom.range.zero_mem
  add_mem' := embedHom.range.add_mem
  smul_mem' n w hw := embedHom.range.zsmul_mem hw n

lemma standard_eq_integer : standardModule=integerModule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro w ⟨i,rfl⟩
    refine ⟨axis i,?_⟩
    simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_apply] using embed_axis i
  · rintro w ⟨v,rfl⟩
    have ha (i : Fin 3) : embed (axis i)∈standardModule := by
      rw [embed_axis,←EuclideanSpace.basisFun_apply]
      exact Submodule.subset_span ⟨i,rfl⟩
    have he : embed v=(v.1:ℤ) • embed (axis 0)+(v.2.1:ℤ) • embed (axis 1)+
        (v.2.2:ℤ) • embed (axis 2) := by
      ext i
      fin_cases i <;> simp [embed,axis]
    rw [he]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (Submodule.smul_mem _ _ (ha 0)) (Submodule.smul_mem _ _ (ha 1)))
      (Submodule.smul_mem _ _ (ha 2))

instance standard_discrete : DiscreteTopology standardModule :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)))
instance standard_isZLattice : IsZLattice ℝ standardModule :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis)))

/-- Absolute covolume1 is established in the fixed STANDARD Euclidean
volume normalization, through the original orthonormal fundamental domain. -/
theorem standard_covolume : ZLattice.covolume standardModule=1 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  rw [ZLattice.covolume_eq_measure_fundamentalDomain standardModule volume
    (ZSpan.isAddFundamentalDomain b volume)]
  calc
    volume.real (ZSpan.fundamentalDomain b)=volume.real (parallelepiped b) :=
      measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped b volume)
    _ = 1 := by
      rw [measureReal_def]
      have h : volume (parallelepiped b)=1 :=
        (EuclideanSpace.basisFun (Fin 3) ℝ).volume_parallelepiped
      rw [h,ENNReal.toReal_one]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma original_le_standard (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    realModule p κ t≤standardModule := by
  rw [standard_eq_integer]
  rintro w ⟨v,hv,he⟩
  exact ⟨v,he⟩

/-- The exact original subgroup index survives the STANDARD embedding
because that additive hom is injective. No coordinate determinant or
extra factor2 is inserted, and no merely abstract cardinality is used. -/
theorem original_relative_index (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) :
    (realModule p κ t).toAddSubgroup.relIndex standardModule.toAddSubgroup=
      (FixedSquarefreeCRT318.modulus p)^2 := by
  rw [standard_eq_integer]
  change ((literalLattice p κ t).map embedHom).relIndex embedHom.range=_
  have hr : embedHom.range=(⊤ : AddSubgroup (Vector ℤ)).map embedHom := by simp
  rw [hr,AddSubgroup.relIndex_map_map_of_injective _ _ embed_injective,
    AddSubgroup.relIndex_top_right]
  exact literal_lattice_index p hp hd hp2 κ t

/-- Absolute covolume of the ACTUAL original integer lattice in the
STANDARD Euclidean metric is exactly M², the already proved original
integer subgroup index. This is not a successive-minima inequality. -/
theorem original_covolume (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) :
    ZLattice.covolume (realModule p κ t)=(FixedSquarefreeCRT318.modulus p:ℝ)^2 := by
  letI := actual_isZLattice p hp κ t
  have h := ZLattice.covolume_div_covolume_eq_relIndex'
    (realModule p κ t) standardModule (original_le_standard p κ t)
  rw [standard_covolume,div_one,original_relative_index p hp hd hp2 κ t,Nat.cast_pow] at h
  exact h

end OriginalCovolumeIndex318
