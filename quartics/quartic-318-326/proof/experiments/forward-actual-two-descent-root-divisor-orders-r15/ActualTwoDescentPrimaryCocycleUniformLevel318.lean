module
public import ActualTwoDescentPrimaryGeometricCocycles318
public import Mathlib.FieldTheory.Galois.Profinite
public section
noncomputable section
namespace ActualTwoDescentPrimaryCocycleUniformLevel318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "Gal" => Field.absoluteGaloisGroup F
local instance : DecidableEq Qbar := Classical.decEq _
open ActualTwoDescentEllipticModel318 ActualTwoDescentFieldAlgebraicClosureHalving318
open ActualTwoDescentFieldGaloisPointAction318 ActualTwoDescentFieldGaloisFixedRational318
open ActualTwoDescentFieldHalvingCocycle318 ActualTwoDescentContinuousEllipticCocycles318
open ActualTwoDescentFullEllipticRepresentation318 ActualTwoDescentFullEllipticHOneKernel318
open groupCohomology
open ActualTwoDescentPowerValuedCocycles318 ActualTwoDescentPowerTorsionBoundaries318
open ActualTwoDescentGeometricPowerTorsion318 ActualTwoDescentFullBoundaryHom318
open ActualTwoDescentHigherFullClassMap318 ActualTwoDescentHigherFullKernel318 ActualTwoDescentHigherFullLifting318

open ActualTwoDescentPrimaryGeometricCocycles318

instance actual_absolute_galois_compact : CompactSpace (Field.absoluteGaloisGroup F) :=
  inferInstanceAs (CompactSpace (Qbar ≃ₐ[F] Qbar))

/-- Compactness of the ACTUAL absolute Galois group makes every locally constant primary-valued cocycle uniformly bounded in torsion order. -/
theorem actual_primary_cocycle_uniform_level (n : F) (hn : n ≠ 0) (z : primaryCocycles n hn) :
    ∃ k : ℕ, ∀ σ : Gal, (2^k) • z.val.val σ=0 := by
  classical
  let R := Set.range (z.val.val : Gal → Point (algebraMap F Qbar n))
  have hR : R.Finite := z.val.property.range_finite
  letI : Finite R := hR.to_subtype
  letI := Fintype.ofFinite R
  have hp (a : R) : ∃ k : ℕ, (2^k) • a.val=0 := by
    obtain ⟨σ,hσ⟩ := a.property
    rw [←hσ]
    exact z.property σ
  let v (a : R) : ℕ := Classical.choose (hp a)
  let N := Finset.univ.sup v
  refine ⟨N,?_⟩
  intro σ
  let a : R := ⟨z.val.val σ,⟨σ,rfl⟩⟩
  exact actual_nsmul_power_mono (Finset.le_sup (Finset.mem_univ a)) (Classical.choose_spec (hp a))

end ActualTwoDescentPrimaryCocycleUniformLevel318
