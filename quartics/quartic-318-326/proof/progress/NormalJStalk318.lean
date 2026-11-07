module
public import NormalJModel318
public import HeightOneDVR318
public section
noncomputable section
namespace NormalJStalk318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) (B:Type) [CommRing B] [IsDomain B]
  [Algebra (OpenJModel318.Base N) B] [Module.Finite (OpenJModel318.Base N) B]
  [Algebra.Etale (OpenJModel318.Base N) B]

/-- Actual codimension-one points in either constructed affine chart have
actual DVR structure sheaf stalks. -/
theorem codimension_one_dvr (hN:N≠0) (j:Fin 2)
    (x:(NormalJModel318.sourceCover N B j).1)
    (hx:((NormalJModel318.sourceCover N B j).2.primeIdealOf x).asIdeal.height=1) :
    IsDiscreteValuationRing
      ((OpenJProjectiveMap318.coverMap N B).normalization.presheaf.stalk x.val) := by
  let U:=NormalJModel318.sourceCover N B j
  let R:=Γ((OpenJProjectiveMap318.coverMap N B).normalization,U)
  let S:=(OpenJProjectiveMap318.coverMap N B).normalization.presheaf.stalk x.val
  let p:=(U.2.primeIdealOf x).asIdeal
  letI:IsDomain R:=(NormalJModel318.chart_properties N B hN j).1
  letI:IsIntegrallyClosed R:=(NormalJModel318.chart_properties N B hN j).2.1
  letI:IsNoetherianRing R:=(NormalJModel318.chart_properties N B hN j).2.2
  letI:=(OpenJProjectiveMap318.coverMap N B).normalization.presheaf.algebra_section_stalk x
  letI:=U.2.isLocalization_stalk x
  letI:=HeightOneDVR318.localization p hx
  let e:Localization.AtPrime p ≃ₐ[R] S:=IsLocalization.algEquiv p.primeCompl _ _
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e

end NormalJStalk318
