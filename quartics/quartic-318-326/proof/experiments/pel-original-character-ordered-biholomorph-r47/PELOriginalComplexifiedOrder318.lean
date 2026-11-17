module
public import PELOriginalPeriodKernelConnection318
public section
noncomputable section
namespace PELOriginalComplexifiedOrder318
open PELQuaternionRealRepresentation318 PELPrincipalOrderCoordinates318
open PELOriginalSymplecticCoordinates318 PELOriginalSiegelNormalization318
open PELOriginalFlatPeriodKernel318 PELOriginalPeriodKernelConnection318
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

/-- Complex-linear extension of the ACTUAL original order representation
in its specified integral symplectic coordinates. -/
@[expose] def split (p : Ambient) : Mat :=
  !![p.1 0+(1+(beta:ℂ))*p.1 1/2,
      (alpha:ℂ)/10*(((beta:ℂ)-5)*p.2 0-2*(beta:ℂ)*p.2 1);
     (alpha:ℂ)/10*(((beta:ℂ)+5)*p.2 0-2*(beta:ℂ)*p.2 1),
      p.1 0+(1-(beta:ℂ))*p.1 1/2]
@[expose] def unsplit (M : Mat) : Ambient :=
  (![(((beta:ℂ)-1)*M 0 0+((beta:ℂ)+1)*M 1 1)/(2*(beta:ℂ)),
      (M 0 0-M 1 1)/(beta:ℂ)],
   ![(M 1 0-M 0 1)/(alpha:ℂ),
      (((beta:ℂ)-5)*M 1 0-((beta:ℂ)+5)*M 0 1)/(2*(alpha:ℂ)*(beta:ℂ))])
lemma alpha_ne : (alpha:ℂ)≠0 := by exact_mod_cast alpha_pos.ne'
lemma unsplit_split (p : Ambient) : unsplit (split p)=p := by
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [unsplit,split] <;> field_simp [alpha_ne,beta_complex_ne] <;> ring
lemma split_unsplit (M : Mat) : split (unsplit M)=M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unsplit,split] <;> field_simp [alpha_ne,beta_complex_ne] <;> ring
@[expose] def splitEquiv : Ambient ≃ₗ[ℂ] Mat where
  toFun := split
  invFun := unsplit
  left_inv := unsplit_split
  right_inv := split_unsplit
  map_add' := by intro p q;ext i j;fin_cases i <;> fin_cases j <;> simp [split] <;> ring
  map_smul' := by intro a p;ext i j;fin_cases i <;> fin_cases j <;> simp [split] <;> ring

/-- Every original integral lattice element is preserved literally,
including all half-integral/quaternionic order-basis denominators. -/
lemma split_integral (p : Pair) : split (integralVector p)=
    fun i j => (representation (embed (fromPair p)) i j:ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [split,integralVector,representation,matrix,embed,fromPair] <;>
    push_cast <;> ring

@[expose] def oriented (M N : Mat) : ℂ :=
  -((M 0 0*N 0 1-M 0 1*N 0 0)+(M 1 0*N 1 1-M 1 1*N 1 0))/(alpha:ℂ)
/-- Full complex bilinear extension of the SAME original polarization,
not a rank-based or scalar-rescaled alternating form. -/
lemma oriented_split (p q : Ambient) : oriented (split p) (split q)=symplectic p q := by
  simp [oriented,split,symplectic,dotProduct,Fin.sum_univ_two]
  field_simp [alpha_ne]
  ring_nf
  rw [beta_complex_sq]
  ring
end PELOriginalComplexifiedOrder318
