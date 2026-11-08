module
public import AlgHomDifferential318
public section
namespace QuadraticCoordinateDerivative318
variable {R S:Type*} [CommRing R] [CommRing S] [Algebra R S]
theorem equation (a b k:R) (u:S):
    KaehlerDifferential.D R S (algebraMap R S a*(algebraMap R S b*u^2)+algebraMap R S k)=
      (algebraMap R S (2*a*b)*u) • KaehlerDifferential.D R S u:=by
  simp only [map_add,pow_two,Derivation.leibniz,Derivation.map_algebraMap,
    add_zero,smul_zero,map_mul,map_ofNat]
  module
section Module
variable {K V:Type*} [CommRing K] [AddCommGroup V] [Module K V]
theorem isolate (a b v:K) (ω η:V) (hv:v*a=1) (h:a • ω=b • η):ω=(v*b) • η:=by
  calc
    ω=(1:K) • ω:=(one_smul _ _).symm
    _=(v*a) • ω:=by rw [hv]
    _=v • (a • ω):=(smul_smul _ _ _).symm
    _=v • (b • η):=by rw [h]
    _=(v*b) • η:=smul_smul _ _ _
end Module
end QuadraticCoordinateDerivative318
