module
public import QuadraticCoordinateDerivative318
public section
noncomputable section
namespace RegularUnitMultiple318
variable {K V:Type*} [CommRing K] [AddCommGroup V] [Module K V]
theorem of_factorizations (u a v:K) (ω ξ η:V) (hv:IsUnit v)
    (ha:ω=(u*a) • η) (hb:ξ=(v*u) • η):∃b:K,ω=b • ξ:=by
  obtain ⟨w,hw⟩:=hv
  refine ⟨(↑w⁻¹:K)*a,?_⟩
  rw [ha,hb,smul_smul,←hw]
  apply congrArg (fun z:K=>z • η)
  calc
    u*a=((↑w⁻¹:K)*w)*(a*u):=by rw [Units.inv_mul,one_mul];ring
    _=((↑w⁻¹:K)*a)*(w*u):=by ring
end RegularUnitMultiple318
