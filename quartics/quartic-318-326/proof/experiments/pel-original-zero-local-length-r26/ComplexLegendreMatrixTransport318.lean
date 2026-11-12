module
public import ComplexSphereMatrixRealization318
public section
noncomputable section
namespace ComplexLegendreMatrixTransport318
open scoped OnePoint
open ComplexProjectiveCrossRatio318 ComplexSphereMatrixRealization318

@[expose] def branch (l:ℂ) : Fin 4→OnePoint ℂ:=![∞,(0:ℂ),(1:ℂ),(l:ℂ)]
@[expose] def quartic (l:ℂ) (v:ℂ×ℂ) : ℂ:=v.2*v.1*(v.1-v.2)*(v.1-l*v.2)
@[expose] def cubic (l z:ℂ) : ℂ:=z*(z-1)*(z-l)
lemma branch_product (l:ℂ) (v:ℂ×ℂ) :
    (∏j:Fin 4,bracket v (lift (branch l j))) = -quartic l v := by
  simp [Fin.prod_univ_succ,branch,lift,bracket,quartic]
  <;> ring

/-- The exact constant comes from the actual projective lifts of the four
marked points. No j-invariant or unmarked curve classification enters. -/
theorem homogeneous_transport {f:OnePoint ℂ≃ₜOnePoint ℂ}
    (A:Realization f) (l m:ℂ) (e:Equiv.Perm (Fin 4))
    (he:∀j,f (branch l (e j))=branch m j) :
    ∃K:ℂ,K≠0 ∧ ∀v:ℂ×ℂ,
      quartic m (matrix A.a A.b A.c A.d v)=K*quartic l v := by
  choose s hs hh using fun j=>A.action (branch l (e j))
  have hh' : ∀j,lift (branch m j)=scale (s j)
      (matrix A.a A.b A.c A.d (lift (branch l (e j)))):=by
    intro j
    simpa only [he j] using hh j
  refine ⟨(∏j:Fin 4,s j)*(A.a*A.d-A.b*A.c)^4,
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun j _=>hs j)) (pow_ne_zero 4 A.det_ne),?_⟩
  intro v
  have hb : ∀j,bracket (matrix A.a A.b A.c A.d v) (lift (branch m j))=
      s j*(A.a*A.d-A.b*A.c)*bracket v (lift (branch l (e j))) := by
    intro j
    rw [hh' j]
    calc
      _ = s j*bracket (matrix A.a A.b A.c A.d v)
        (matrix A.a A.b A.c A.d (lift (branch l (e j)))):=by
          simp only [bracket,scale];ring
      _ = _ := by rw [bracket_matrix];ring
  have hp:=congrArg (fun q:Fin 4→ℂ=>∏j,q j) (funext hb)
  simp only [Finset.prod_mul_distrib] at hp
  have perm : (∏j:Fin 4,bracket v (lift (branch l (e j))))=
      ∏j:Fin 4,bracket v (lift (branch l j)):=
    Equiv.prod_comp e (fun j=>bracket v (lift (branch l j)))
  rw [perm,branch_product,branch_product] at hp
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hp
  linear_combination -hp

/-- The affine formula is valid on precisely the locus with finite image.
The fourth power is the homogeneous degree, not an inferred weight. -/
theorem affine_transport (a b c d l m K z:ℂ) (hd:c*z+d≠0)
    (h:quartic m (matrix a b c d (z,1))=K*quartic l (z,1)) :
    cubic m ((a*z+b)/(c*z+d))=K*cubic l z/(c*z+d)^4 := by
  dsimp [quartic,matrix,cubic] at h ⊢
  field_simp [hd]
  linear_combination h

/-- The y-coordinate is linear and odd in the original y. Its square is
proved from the full branch polynomial identity, not equality of j. -/
theorem ordinate_square (a b c d l m K u z y:ℂ) (hd:c*z+d≠0)
    (hu:u^2=K) (hy:y^2=cubic l z)
    (h:quartic m (matrix a b c d (z,1))=K*quartic l (z,1)) :
    (u*y/(c*z+d)^2)^2=cubic m ((a*z+b)/(c*z+d)) := by
  rw [affine_transport a b c d l m K z hd h]
  rw [div_pow,mul_pow,hu,hy]
  ring
lemma ordinate_neg (u c d z y:ℂ) :
    u*(-y)/(c*z+d)^2=-(u*y/(c*z+d)^2):=by ring
end ComplexLegendreMatrixTransport318
