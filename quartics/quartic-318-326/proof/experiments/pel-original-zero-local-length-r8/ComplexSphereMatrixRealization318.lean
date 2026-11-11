module
public import ComplexSphereActualCrossRatio318
public section
noncomputable section
namespace ComplexSphereMatrixRealization318
open scoped OnePoint
open ComplexProjectiveCrossRatio318 ComplexSphereAffineNormalization318
open ComplexSphereFourPointNormalization318 ComplexSphereActualCrossRatio318

/-- A matrix acting on the actual sphere map, including its points at infinity.
The pointwise nonzero scale is projective, not a chosen affine denominator. -/
structure Realization (f : OnePoint ℂ ≃ₜ OnePoint ℂ) where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  det_ne : a*d-b*c≠0
  action : ∀p, ∃s:ℂ, s≠0 ∧ lift (f p)=scale s (matrix a b c d (lift p))

@[expose] def identity : Realization (Homeomorph.refl (OnePoint ℂ)) where
  a:=1; b:=0; c:=0; d:=1
  det_ne:=by norm_num
  action p:=⟨1,one_ne_zero,by simp [scale,matrix]⟩

@[expose] def affine (a b:ℂ) (ha:a≠0) : Realization (affineSphere a b ha) where
  a:=a; b:=b; c:=0; d:=1
  det_ne:=by simpa using ha
  action:=affine_action a b ha

@[expose] def inversion : Realization SphereInversion318.inversionHomeomorph where
  a:=0; b:=1; c:=1; d:=0
  det_ne:=by norm_num
  action:=inversion_action

@[expose] def compose {f g:OnePoint ℂ≃ₜOnePoint ℂ}
    (A:Realization f) (B:Realization g) : Realization (f.trans g) where
  a:=B.a*A.a+B.b*A.c
  b:=B.a*A.b+B.b*A.d
  c:=B.c*A.a+B.d*A.c
  d:=B.c*A.b+B.d*A.d
  det_ne:=by
    have h:(B.a*A.a+B.b*A.c)*(B.c*A.b+B.d*A.d)-
        (B.a*A.b+B.b*A.d)*(B.c*A.a+B.d*A.c)=
        (B.a*B.d-B.b*B.c)*(A.a*A.d-A.b*A.c):=by ring
    rw [h]
    exact mul_ne_zero B.det_ne A.det_ne
  action p:=by
    obtain ⟨s,hs,he⟩:=A.action p
    obtain ⟨t,ht,hf⟩:=B.action (f p)
    refine ⟨t*s,mul_ne_zero ht hs,?_⟩
    change lift (g (f p))=_
    rw [hf,he]
    apply Prod.ext <;> simp only [scale,matrix] <;> ring

@[expose] def inverse {f:OnePoint ℂ≃ₜOnePoint ℂ}
    (A:Realization f) : Realization f.symm where
  a:=A.d; b:=-A.b; c:=-A.c; d:=A.a
  det_ne:=by simpa only [neg_mul_neg, mul_comm A.d A.a] using A.det_ne
  action p:=by
    obtain ⟨s,hs,he⟩:=A.action (f.symm p)
    rw [Homeomorph.apply_symm_apply] at he
    refine ⟨(s*(A.a*A.d-A.b*A.c))⁻¹,inv_ne_zero (mul_ne_zero hs A.det_ne),?_⟩
    rw [he]
    apply Prod.ext <;> simp only [scale,matrix] <;>
      field_simp [hs,A.det_ne] <;> ring

@[expose] def pole (p:OnePoint ℂ) : Realization (poleCoordinate p) := by
  induction p using OnePoint.rec with
  | infty=>exact identity
  | coe z=>exact compose (affine 1 (-z) one_ne_zero) inversion

@[expose] def fourPoints (p:Fin 4→OnePoint ℂ) (hp:Function.Injective p) :
    Realization (normalization p hp):=
  compose (pole (p 0)) (affine
    (finiteCoordinate p hp 1-finiteCoordinate p hp 0)⁻¹
    (-finiteCoordinate p hp 0/(finiteCoordinate p hp 1-finiteCoordinate p hp 0))
    (inv_ne_zero (denominator_ne p hp)))

/-- No denominator is assumed nonzero: finiteness of the actual image
forces it, and then determines the genuine fractional-linear value. -/
theorem finite_value {f:OnePoint ℂ≃ₜOnePoint ℂ} (A:Realization f)
    (z w:ℂ) (h:f (z:OnePoint ℂ)=(w:OnePoint ℂ)) :
    A.c*z+A.d≠0 ∧ w=(A.a*z+A.b)/(A.c*z+A.d) := by
  obtain ⟨s,hs,he⟩:=A.action (z:OnePoint ℂ)
  rw [h] at he
  have hx:=congrArg Prod.fst he
  have hy:=congrArg Prod.snd he
  simp only [lift,scale,matrix,mul_one] at hx hy
  have hd:A.c*z+A.d≠0:=by intro hd; rw [hd,mul_zero] at hy; norm_num at hy
  refine ⟨hd,?_⟩
  apply (eq_div_iff hd).2
  rw [hx]
  calc
    s*(A.a*z+A.b)*(A.c*z+A.d)=(A.a*z+A.b)*(s*(A.c*z+A.d)):=by ring
    _ = A.a*z+A.b:=by rw [←hy,mul_one]
end ComplexSphereMatrixRealization318
