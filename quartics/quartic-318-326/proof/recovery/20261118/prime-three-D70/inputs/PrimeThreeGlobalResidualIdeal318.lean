module
public import IdealSheafOpenKernel318
public import PrimeThreeSelectedFirstUResidualCenter318
public import Mathlib.AlgebraicGeometry.Noetherian
public section
noncomputable section
namespace PrimeThreeGlobalResidualIdeal318
open AlgebraicGeometry CategoryTheory
open PrimeThreeSelectedFirstUResidualCenter318 OriginalPrimeThreeFirstOrderPoint318
open OriginalPrimeThreeFirstUNativeChart318 OriginalPrimeThreeNativeReesProj318

/-- The actual F9 point on the selected first-U chart. -/
@[expose] def residualPointMorphism : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of LocalU) :=
  Spec.map (CommRingCat.ofHom localResidualPoint)

/-- This point lies on the actual first Rees Proj via its already identified
arithmetic first-U open. It is not an abstract point with the same residue field. -/
@[expose] def globalResidualPoint : Spec (CommRingCat.of K) ⟶ actualReesProj :=
  residualPointMorphism ≫ explicitFirstUInclusion

instance residualPoint_quasiCompact : QuasiCompact globalResidualPoint := inferInstance

/-- Native quasi-coherent ideal-sheaf DATA on the whole first blowup,
constructed as the kernel of the actual residual point morphism. Its support
is initially the closure of that point; closedness is not assumed. -/
@[expose] def globalResidualIdeal : actualReesProj.IdealSheafData := globalResidualPoint.ker

/-- The actual ring ideal, transported into the canonical affine sections. -/
@[expose] def localResidualIdeal : (Spec (CommRingCat.of LocalU)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    (localCenter.comap (Scheme.ΓSpecIso (CommRingCat.of LocalU)).hom.hom)

theorem residualPoint_kernel : residualPointMorphism.ker = localResidualIdeal := by
  rw [residualPointMorphism, IdealSheafOpenKernel318.specMap_kernel]
  rw [← localCenter_eq_kernel]
  rfl

/-- Exact restriction to the first-U arithmetic chart. This is not merely
an inclusion or a condition on its set of closed points. -/
theorem globalResidualIdeal_on_firstU :
    globalResidualIdeal.comap explicitFirstUInclusion = localResidualIdeal := by
  change (residualPointMorphism ≫ explicitFirstUInclusion).ker.comap
    explicitFirstUInclusion = _
  rw [IdealSheafOpenKernel318.kernel_comap_open_comp, residualPoint_kernel]

/-- Exact global support statement, retaining closure until global
closedness/disjointness from the other two first charts is established. -/
theorem globalResidualIdeal_support :
    (globalResidualIdeal.support : Set actualReesProj) = closure (Set.range globalResidualPoint) :=
  Scheme.Hom.support_ker globalResidualPoint

end PrimeThreeGlobalResidualIdeal318
