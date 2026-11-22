module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Away.Basic

public section

noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace SelectedActualComplexPrincipalOpenScalarChange318

variable (k C B O : Type*) [CommRing k] [CommRing C] [CommRing B] [CommRing O]
  [Algebra k C] [Algebra k B] [Algebra k O] [Algebra B O] [IsScalarTower k B O]

/-- The literal map on base-changed arithmetic chart sections. -/
abbrev scalarOpenMap : C ⊗[k] B →ₐ[C] C ⊗[k] O :=
  Algebra.TensorProduct.map (AlgHom.id C C) (IsScalarTower.toAlgHom k B O)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The arithmetic ordinary principal open, after actual scalar
change, is exactly the corresponding ordinary principal open of
the same scalar-changed affine chart. -/
theorem scalar_change_principal_open (d : B) [IsLocalization.Away d O] :
    letI : Algebra (C ⊗[k] B) (C ⊗[k] O) :=
      (scalarOpenMap k C B O).toRingHom.toAlgebra
    IsLocalization.Away
      ((Algebra.TensorProduct.includeRight : B →ₐ[k] C ⊗[k] B) d)
      (C ⊗[k] O) := by
  let S := C ⊗[k] B
  let W := C ⊗[k] O
  let f : S →ₐ[C] W := scalarOpenMap k C B O
  letI : Algebra S W := f.toRingHom.toAlgebra
  letI : Algebra B W := Algebra.compHom W (algebraMap B O)
  letI : IsScalarTower C S W := IsScalarTower.of_algebraMap_eq fun c => (f.commutes c).symm
  letI : IsScalarTower B O W := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower B S W := IsScalarTower.of_algebraMap_eq fun b => by
    change (1 : C) ⊗ₜ[k] (algebraMap B O b) = f ((1 : C) ⊗ₜ[k] b)
    symm
    exact Algebra.TensorProduct.map_tmul _ _ 1 b
  letI : IsScalarTower k S W := IsScalarTower.to₁₃₄ k C S W
  have hPush : Algebra.IsPushout B O S W :=
    (Algebra.IsPushout.comp_iff k B C).mp (inferInstance : Algebra.IsPushout k O C W)
  letI : Algebra.IsPushout B S O W := Algebra.IsPushout.symm hPush
  have hLoc : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers d)) W :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers d) O).mpr inferInstance
  change IsLocalization
    (Submonoid.powers ((Algebra.TensorProduct.includeRight : B →ₐ[k] S) d)) W
  have h : Algebra.algebraMapSubmonoid S (Submonoid.powers d) =
      Submonoid.powers ((Algebra.TensorProduct.includeRight : B →ₐ[k] S) d) := by
    unfold Algebra.algebraMapSubmonoid
    exact Submonoid.map_powers _ _
  exact h ▸ hLoc

end SelectedActualComplexPrincipalOpenScalarChange318

#print axioms SelectedActualComplexPrincipalOpenScalarChange318.scalar_change_principal_open
