module
public import ActualDualUnitNormIdentification318
public import OpenUnitNorm318
public section
noncomputable section
namespace OriginalAllOpenDualNorm318
open AlgebraicGeometry CategoryTheory Opposite
open SquareZeroUnit318 DualUnitFactorization318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    (hY : NormalAffineBasis318.HasBasis Y)
    (hfinite : letI := AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
/-- Full dual-section unit norm on EVERY original target open, including empty
and disconnected opens. The next theorem checks every original restriction. -/
@[expose] def norm (U : Y.Opens) : (Dual Γ(X,f ⁻¹ᵁ U))ˣ →* (Dual Γ(Y,U))ˣ :=
  DualUnitNormConstruction318.norm (Units.map (OpenDominantNorm318.norm f hY U))
    (OpenDominantTrace318.trace f hY hfinite U)
lemma coefficient_value (U : Y.Opens) (a : Γ(X,f ⁻¹ᵁ U)ˣ) :
    norm f hY hfinite U (lift _ a) =
      lift _ (Units.map (OpenDominantNorm318.norm f hY U) a) :=
  DualUnitNormConstruction318.coefficient_value _ _ a
lemma infinitesimal_value (U : Y.Opens) (a : Γ(X,f ⁻¹ᵁ U)) :
    norm f hY hfinite U (unit _ a) = unit _ (OpenDominantTrace318.trace f hY hfinite U a) :=
  DualUnitNormConstruction318.infinitesimal_value _ _ a
lemma restrict {U V : Y.Opens} (i : U ⟶ V) (z : (Dual Γ(X,f ⁻¹ᵁ V))ˣ) :
    Units.map (SquareZeroUnit318.map Γ(Y,V) (Y.presheaf.map i.op).hom).toMonoidHom
      (norm f hY hfinite V z) =
    norm f hY hfinite U
      (Units.map (SquareZeroUnit318.map Γ(X,f ⁻¹ᵁ V)
        (X.presheaf.map (homOfLE (f.preimage_mono i.le)).op).hom).toMonoidHom z) := by
  apply DualUnitNormConstruction318.naturality
  · intro a
    apply Units.ext
    exact OpenDominantNorm318.restrict f hY i a.val
  · intro a
    exact OpenDominantTrace318.restrict f hY hfinite i a
/-- The construction is not merely a formula attached to trace. On ANY
original affine open with an actual finite basis of the ENTIRE preimage ring,
it equals the genuine determinant norm of that original dual algebra. -/
lemma determinant_agreement (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bs : letI := (f.app U).hom.toAlgebra
      Module.Basis ι Γ(Y,U) Γ(X,f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    letI := OriginalDualAlgebraNormTrace318.actualAlgebra Γ(Y,U) Γ(X,f ⁻¹ᵁ U)
    norm f hY hfinite U = Units.map (Algebra.norm (DualNumber Γ(Y,U))) := by
  letI := (f.app U).hom.toAlgebra
  letI := OriginalDualAlgebraNormTrace318.actualAlgebra Γ(Y,U) Γ(X,f ⁻¹ᵁ U)
  letI := Module.Free.of_basis bs
  letI := Module.Finite.of_basis bs
  rw [ActualDualUnitNormIdentification318.norm_eq]
  change DualUnitNormConstruction318.norm _ _ = DualUnitNormConstruction318.norm _ _
  congr 1
  · ext a
    apply Units.ext
    exact (OriginalFiniteFreeDualTransfer318.norm_eq f hY U hU bs a.val).symm
  · ext a
    exact (OriginalFiniteFreeDualTransfer318.trace_eq f hY hfinite U hU bs a).symm
end OriginalAllOpenDualNorm318
