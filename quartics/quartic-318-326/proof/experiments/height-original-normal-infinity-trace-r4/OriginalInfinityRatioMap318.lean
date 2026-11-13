module
public import OriginalInfinityRatioParameters318
public section
noncomputable section
namespace OriginalInfinityRatioMap318
open Polynomial FourRootRatioOrder318 OriginalInfinityRatioParameters318
open scoped TensorProduct
variable (V : Type*) [CommRing V] (d a : Fin 4 → V)
abbrev Order := RatioOrder (common V d a) (ratios V d a)

/-- The finite map from the actual localized original order into its
ratio-order modification, with all16 coefficient directions retained. -/
@[expose] def baseChangedMap :
    Base V d a ⊗[V[X]] DVRNormalizedInfinityOrder318.Order V d a →ₐ[Base V d a] Order V d a :=
  (FourRootRatioOrder318.map (common V d a) (ratios V d a)).comp (baseChangeEquiv V d a).toAlgHom

/-- Actual original reciprocal source map with the exact polynomial scalar
map. This uses the full base-change morphism and original marked roots. -/
@[expose] def sourceMap : DVRNormalizedInfinityOrder318.Order V d a →ₐ[V[X]] Order V d a :=
  ((baseChangedMap V d a).restrictScalars V[X]).comp Algebra.TensorProduct.includeRight

lemma sourceMap_scalar (p : V[X]) : sourceMap V d a
    (algebraMap V[X] (DVRNormalizedInfinityOrder318.Order V d a) p)=
      algebraMap V[X] (Order V d a) p := (sourceMap V d a).commutes p

lemma originalEquiv_root (i : Fin 4) : originalEquiv V d a
    (FourRootOrderSigns318.generator (fun j => algebraMap V[X] (Base V d a)
      (DVRNormalizedInfinityOrder318.coefficient V d a j)) i)=
      FourRootOrderSigns318.generator (original (common V d a) (ratios V d a)) i := by
  rw [originalEquiv,FourRootUnitScale318.four_generator]
  simp only [Units.val_one,one_smul]

lemma sourceMap_root (i : Fin 4) : sourceMap V d a
    (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient V d a) i)=
      marked (common V d a) (ratios V d a) i := by
  change FourRootRatioOrder318.map (common V d a) (ratios V d a)
    (originalEquiv V d a
      (FourRootSignBaseChange318.coefficientMap (DVRNormalizedInfinityOrder318.coefficient V d a)
        (Base V d a) (FourRootOrderSigns318.generator (DVRNormalizedInfinityOrder318.coefficient V d a) i))) = _
  rw [FourRootSignBaseChange318.coefficientMap_generator,originalEquiv_root,map_root]
end OriginalInfinityRatioMap318
