module
public import FourRootCoordinateOverlap318
public import ReciprocalCoordinateDifferential318
public section
noncomputable section
namespace FourRootOverlapOriginalDifferential318
open FourRootCoordinateOverlap318
variable (b:Fin 4→ℂ)
/-- The original t coordinate has its true differential already in the
ACTUAL regular overlap ring, before passing to any fraction field or
comparing meromorphic frames. The inverse u is regular on this overlap. -/
theorem original_dt:
    KaehlerDifferential.D ℂ (InfinityOverlap b)
      (toInfinityBase b (FourRootAffineCoordinateRing318.coordinate b none))=
    (-(2:InfinityOverlap b)*(ui b)^3) •
      KaehlerDifferential.D ℂ (InfinityOverlap b) (u b):=by
  have hs:(u b)^2*(ui b)^2=algebraMap ℂ (InfinityOverlap b) 1:=by
    rw [←mul_pow,u_ui,one_pow,map_one]
  have hd:=ReciprocalCoordinateDifferential318.D_of_inverse (R:=ℂ)
    ((ui b)^2) (u b) (ui b) 1 (u_ui b) hs
  rw [toInfinityBase_t,map_add,Derivation.map_algebraMap,zero_add]
  calc
    _=-(2*ui b*(ui b)^2) • KaehlerDifferential.D ℂ (InfinityOverlap b) (u b):=hd
    _=_:=by congr 1;ring
/-- Multiplying by the genuine original u³ clears exactly the pole of
the original dt, with coefficient -2 in the SAME actual du generator. -/
theorem cleared_original_dt:
    (u b)^3 • KaehlerDifferential.D ℂ (InfinityOverlap b)
      (toInfinityBase b (FourRootAffineCoordinateRing318.coordinate b none))=
      -(2:InfinityOverlap b) • KaehlerDifferential.D ℂ (InfinityOverlap b) (u b):=by
  rw [original_dt,smul_smul]
  have hc:(u b)^3*(-(2:InfinityOverlap b)*(ui b)^3)=-(2:InfinityOverlap b):=by
    calc
      (u b)^3*(-(2:InfinityOverlap b)*(ui b)^3)=
        -(2:InfinityOverlap b)*((u b)*(ui b))^3:=by ring
      _=-(2:InfinityOverlap b):=by rw [u_ui,one_pow,mul_one]
  rw [hc]
end FourRootOverlapOriginalDifferential318
