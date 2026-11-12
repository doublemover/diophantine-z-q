module
public import OpenJAffineScheme318
public section
noncomputable section
namespace AffineEquationFunctor318
open ShortAffineJacobian318 MvPolynomial
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Literal solutions over an actual algebra, with the given base coefficients. -/
@[expose] def Solutions (A B : R) :=
  {p : S × S // p.2^2-p.1^3-algebraMap R S A*p.1-algebraMap R S B=0}

@[expose] def ofHom (A B : R) (f : Ring A B →ₐ[R] S) : Solutions (S := S) A B :=
  ⟨(f (x A B),f (y A B)),by
    have hh := congrArg f (relation A B)
    simpa only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes] using hh⟩

@[expose] def toHom (A B : R) (p : Solutions (S := S) A B) : Ring A B →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval ![p.val.1,p.val.2]) (by
    have hk : Ideal.span (Set.range (equations A B)) ≤
        RingHom.ker (aeval ![p.val.1,p.val.2] : MvPolynomial (Fin 2) R →ₐ[R] S) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      change aeval ![p.val.1,p.val.2] (equation A B)=0
      simpa [equation] using p.property
    intro f hf
    exact hk hf)

lemma toHom_x (A B : R) (p : Solutions (S := S) A B) : toHom A B p (x A B)=p.val.1 := by
  simp [toHom,x,Ideal.Quotient.lift_mk]
lemma toHom_y (A B : R) (p : Solutions (S := S) A B) : toHom A B p (y A B)=p.val.2 := by
  simp [toHom,y,Ideal.Quotient.lift_mk]

/-- The actual coordinate-ring homomorphism is determined by the two coordinate values. -/
theorem hom_ext (A B : R) (f g : Ring A B →ₐ[R] S)
    (hx : f (x A B)=g (x A B)) (hy : f (y A B)=g (y A B)) : f=g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · exact hx
  · exact hy

/-- Genuine universal property of the actual affine coordinate ring. -/
@[expose] def solutionEquiv (A B : R) : (Ring A B →ₐ[R] S) ≃ Solutions (S := S) A B where
  toFun := ofHom A B
  invFun := toHom A B
  left_inv f := by
    apply hom_ext
    · exact toHom_x A B (ofHom A B f)
    · exact toHom_y A B (ofHom A B f)
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact toHom_x A B p
    · exact toHom_y A B p

variable {T : Type*} [CommRing T] [Algebra R T]

/-- Literal solution transport under a genuine algebra homomorphism. -/
@[expose] def mapSolution (A B : R) (φ : S →ₐ[R] T) (p : Solutions (S := S) A B) :
    Solutions (S := T) A B := ⟨(φ p.val.1,φ p.val.2),by
      have hh := congrArg φ p.property
      simpa only [map_sub,map_pow,map_mul,map_zero,AlgHom.commutes] using hh⟩

/-- The genuine universal property is natural in the coefficient algebra. -/
theorem solutionEquiv_natural (A B : R) (φ : S →ₐ[R] T) (f : Ring A B →ₐ[R] S) :
    solutionEquiv A B (φ.comp f)=mapSolution A B φ (solutionEquiv A B f) := rfl

end AffineEquationFunctor318
