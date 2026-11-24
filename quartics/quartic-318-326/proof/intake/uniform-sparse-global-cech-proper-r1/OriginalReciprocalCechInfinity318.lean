module
public import OriginalSparseActualBranch318
public section
noncomputable section
namespace OriginalReciprocalCechInfinity318
open OriginalUniformSparseReciprocalChart318
variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
/-- Reciprocal coordinate differential in the actual module of Kähler differentials. -/
theorem differential (x v : A) (hx : x*v=1) :
    KaehlerDifferential.D k A v= -(v^2 • KaehlerDifferential.D k A x) := by
  have h:=congrArg (KaehlerDifferential.D k A) hx
  rw [Derivation.leibniz,Derivation.map_one_eq_zero] at h
  have hh:=congrArg (fun z=>v•z) h
  simp only [smul_add,smul_smul,smul_zero,mul_comm v x,hx,one_smul] at hh
  rw [pow_two]; exact eq_neg_of_add_eq_zero_left hh
/-- Both Hodge forms extend across infinity with the literal reciprocal coefficients:
dx/y=−v dw_base/w and x dx/y=−dw_base/w (dw_base=dv). -/
theorem hodge_frame (x v y w iy iw : A) (hx : x*v=1) (hw : w=y*v^3)
    (hy : y*iy=1) (hu : w*iw=1) :
    iy • KaehlerDifferential.D k A x =
      (-v*iw) • KaehlerDifferential.D k A v ∧
    (x*iy) • KaehlerDifferential.D k A x =
      (-iw) • KaehlerDifferential.D k A v := by
  rw [hw] at hu
  have hi : iy=v^3*iw := by linear_combination (v^3*iw)*hy-iy*hu
  rw [differential x v hx]
  constructor
  · rw [hi,smul_neg,smul_smul,←neg_smul]
    congr 1
    ring
  · rw [hi,smul_neg,smul_smul,←neg_smul]
    congr 1
    linear_combination v^2*iw*hx
omit [Algebra k A] in
/-- On the overlap, keeping x fixed is EXACTLY keeping the reciprocal coordinate
fixed. At its two zeros v=0, the same ordinary lift extends uniquely since 2w
is a unit. No second local y-splitting, hence no extra Čech pole at infinity. -/
theorem fix_reciprocal (x v dx dv : A) (hx : x*v=1) (h : x*dv+v*dx=0) :
    dx=0 ↔ dv=0 := by
  constructor
  · intro hz
    rw [hz,mul_zero,add_zero] at h
    linear_combination v*h-dv*hx
  · intro hz
    rw [hz,mul_zero,zero_add] at h
    linear_combination x*h-dx*hx
omit [Algebra k A] in
theorem two_infinity_lifts (s t ds : A) (hs : IsUnit s) (h2 : IsUnit (2:A)) :
    s^2=reverse s t 0 ∧ (-s)^2=reverse s t 0 ∧
    (∀ dw, (2*s)*dw=2*s*ds ↔ dw=ds) ∧
    (∀ dw, (2*(-s))*dw=2*s*ds ↔ dw= -ds) := by
  obtain ⟨hp,hm,up,um⟩:=infinity_sections s t h2 hs
  refine ⟨hp,hm,?_,?_⟩
  · intro dw; exact up.mul_right_inj
  · intro dw; rw [show 2*s*ds=(2*(-s))*(-ds) by ring]; exact um.mul_right_inj
end OriginalReciprocalCechInfinity318
#print axioms OriginalReciprocalCechInfinity318.hodge_frame
#print axioms OriginalReciprocalCechInfinity318.two_infinity_lifts
