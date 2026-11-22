module
public import ActualGaussianWeberMixedPolynomial318
public section
noncomputable section

namespace ActualGaussianWeberMixedFirstJet318

open ActualGaussianWeberHenselianChart318 ActualGaussianWeberMixedPolynomial318

variable {R : Type*} [CommRing R]

/-- Exact first jet of the actual mixed abscissa, before passing
to any completed ring. Residue second-order terms are exhibited as
a multiple of the square of the original origin parameter t. -/
theorem mixed_firstJet {t w A B u beta : R} (hW : w=t^3*u)
    (hU : (1+t*w)*u=1) (hBeta : (1-A*t^2*u)*beta=1) :
    ∃ q : R, A+t*u*beta^2*H t w A B=A+(2*B)*t+t^2*q := by
  let U := -(w*u)
  let T := A*t*u*beta
  let D := (3*A^2-1)-(A^3+A)*t^2*u
  have eU : u-1=t*U := by
    unfold U
    linear_combination hU
  have eT : beta-1=t*T := by
    unfold T
    linear_combination hBeta
  have eD : H t w A B-2*B=t*D := by
    unfold H D
    rw [hW]
    ring
  let q := U*beta^2*H t w A B+T*(beta+1)*H t w A B+D
  have e : u*beta^2*H t w A B-2*B=t*q := by
    calc
      _ = (u-1)*beta^2*H t w A B+
          (beta-1)*(beta+1)*H t w A B+(H t w A B-2*B) := by ring
      _ = _ := by rw [eU,eT,eD]; unfold q; ring
  exact ⟨q,by linear_combination t*e⟩

variable {F : Type*} [Field F]

/-- The actual signed stock mixed slope (not a free tangent model)
has the same first jet, on the explicit nonvertical branch. -/
theorem stock_mixed_firstJet {t w A B u beta : F}
    (h₀ : identityChart t w) (hQ : B^2=A^3-A) (ht : t≠0) (hw : w≠0)
    (hW : w=t^3*u) (hD : (t-A*w)*beta=t)
    (hU : (1+t*w)*u=1) (hBeta : (1-A*t^2*u)*beta=1) :
    ∃ q : F, (-(1+B*w)/(t-A*w))^2-t/w-A=A+(2*B)*t+t^2*q := by
  obtain ⟨_,hX,_⟩ := scaled_chord h₀ hQ ht hw hW hD
  obtain ⟨q,hq⟩ := mixed_firstJet hW hU hBeta (B:=B)
  refine ⟨q,?_⟩
  linear_combination hX+hq

end ActualGaussianWeberMixedFirstJet318
