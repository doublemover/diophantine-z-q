module
public import WidthQParameter318
public section
noncomputable section
open UpperHalfPlane Function Filter Topology GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open WidthQParameter318
open scoped MatrixGroups
namespace RotatedProjection318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

@[expose] def rotatedMap (N:ℕ) (g:SL(2,ℤ)) : UpperHalfPlane→Base (image N) :=
  fun tau=>quotientMap N (g•tau)

@[expose] def neighborhood (N:ℕ) (g:SL(2,ℤ)) : Set (Base (image N)) :=
  rotatedMap N g '' high 2

theorem rotated_continuous (N:ℕ) (g:SL(2,ℤ)) : Continuous (rotatedMap N g) := by
  have h:Continuous (fun tau:UpperHalfPlane=>g•tau) :=
    (continuous_const_smul (g:GL (Fin 2) ℝ)).congr (fun tau=>(ModularGroup.sl_moeb g tau).symm)
  exact continuous_quotient_mk'.comp h

theorem rotated_open (N:ℕ) (g:SL(2,ℤ)) : IsOpenMap (rotatedMap N g) := by
  have hh:IsOpenMap (fun tau:UpperHalfPlane=>g•tau) :=
    (Homeomorph.smul (g:GL (Fin 2) ℝ)).isOpenMap
  exact MulAction.isOpenQuotientMap_quotientMk.isOpenMap.comp hh

theorem neighborhood_open (N:ℕ) (g:SL(2,ℤ)) : IsOpen (neighborhood N g) :=
  rotated_open N g _ (high_open 2)

@[expose] def projection (N:ℕ) (g:SL(2,ℤ)) : high 2→neighborhood N g :=
  fun tau=>⟨rotatedMap N g tau,⟨tau,tau.property,rfl⟩⟩

theorem projection_surjective (N:ℕ) (g:SL(2,ℤ)) : Surjective (projection N g) := by
  rintro ⟨b,tau,htau,rfl⟩
  exact ⟨⟨tau,htau⟩,rfl⟩

theorem projection_continuous (N:ℕ) (g:SL(2,ℤ)) : Continuous (projection N g) :=
  ((rotated_continuous N g).comp continuous_subtype_val).subtype_mk _

theorem projection_open (N:ℕ) (g:SL(2,ℤ)) : IsOpenMap (projection N g) :=
  ((rotated_open N g).domRestrict (high_open 2)).codRestrict _

theorem projection_quotient (N:ℕ) (g:SL(2,ℤ)) : IsQuotientMap (projection N g) :=
  (projection_open N g).isQuotientMap (projection_continuous N g) (projection_surjective N g)

end RotatedProjection318
