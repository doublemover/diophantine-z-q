module
public import Mathlib.Tactic
public section
namespace ReciprocalBicanonicalIdentity318
variable {S : Type*} [CommRing S]

theorem cleared (c k C U P D d : S) (hk : c*k=1) (hD : D*d=1)
    (hP : c^7*D=C*U^8*P) :
    U^6*(P*(4*C*k^5*U^2*d))=4*c^2 := by
  calc
    _=4*k^5*(C*U^8*P)*d := by ring
    _=4*k^5*(c^7*D)*d := by rw [←hP]
    _=4*c^2*(c*k)^5*(D*d) := by ring
    _=4*c^2 := by rw [hk,hD];ring

theorem factor_cleared (U V T c : S) (hU : U*V=1) (hT : U^2*T=c) :
    U^6*(-(2*V*T))^2=4*c^2 := by
  calc
    _=4*(U*V)^2*(U^2*T)^2 := by ring
    _=4*c^2 := by rw [hU,hT];ring

theorem q1_relation (c k C U T d : S) (hk : c*k=1) (hT : U^2*T=c) :
    T*(4*C*k^5*U^2*d)=4*C*k^4*d := by
  calc
    _=4*C*k^4*((U^2*T)*k)*d := by ring
    _=4*C*k^4*d := by rw [hT,hk];ring
end ReciprocalBicanonicalIdentity318
