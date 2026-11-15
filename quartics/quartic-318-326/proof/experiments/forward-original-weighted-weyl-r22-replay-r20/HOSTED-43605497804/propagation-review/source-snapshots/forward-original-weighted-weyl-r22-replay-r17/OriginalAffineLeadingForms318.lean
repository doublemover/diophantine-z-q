module
public import OriginalQuadraticIntegerFibers318
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public section
noncomputable section
namespace OriginalAffineLeadingForms318
open MvPolynomial TernaryQuadraticLineCover318 OriginalReducedResidueBounds318
set_option maxHeartbeats 6500000
variable {F : Type*} [Field F]

@[expose] def row (a b c : F) : MvPolynomial (Fin 2) F := C c+C a*X 0+C b*X 1
@[expose] def leadingFirst (κ : F) (u v z : Vector F) : MvPolynomial (Fin 2) F :=
  C κ*(row u.2.2 v.2.2 z.2.2)^2
@[expose] def quadratic (κ t : F) (y : Vector F) : F := κ*(t+2)*y.2.2^2-2*y.1*y.2.1
@[expose] def leadingSecond (κ t : F) (u v z : Vector F) : MvPolynomial (Fin 2) F :=
  C (κ*(t+2))*(row u.2.2 v.2.2 z.2.2)^2-
    2*(row u.1 v.1 z.1)*(row u.2.1 v.2.1 z.2.1)
@[expose] def simultaneousLeading (κ t : F) (u v z : Vector F) :=
  leadingFirst κ u v z*leadingSecond κ t u v z

lemma row_eval (a b c i j : F) : eval ![i,j] (row a b c)=c+a*i+b*j := by
  simp [row]

lemma second_eval (κ t : F) (u v z : Vector F) (i j : F) :
    eval ![i,j] (leadingSecond κ t u v z)=quadratic κ t (fieldSynthesis u v z (i,j,1)) := by
  simp [leadingSecond,row,quadratic,fieldSynthesis]
  ring

/-- A homogeneous quadratic is determined by six evaluations on this
actual affine coefficient plane. The factor2 is kept explicitly. -/
lemma affine_reconstruction (κ t : F) (u v z : Vector F) (a b c : F) :
    2*quadratic κ t (fieldSynthesis u v z (a,b,c))=
      (a^2+a*c-2*a*b)*quadratic κ t (fieldSynthesis u v z (1,0,1))+
      (a^2-a*c)*quadratic κ t (fieldSynthesis u v z (-1,0,1))+
      (b^2+b*c-2*a*b)*quadratic κ t (fieldSynthesis u v z (0,1,1))+
      (b^2-b*c)*quadratic κ t (fieldSynthesis u v z (0,-1,1))+
      2*a*b*quadratic κ t (fieldSynthesis u v z (1,1,1))+
      (2*c^2-2*a^2-2*b^2+2*a*b)*quadratic κ t (fieldSynthesis u v z (0,0,1)) := by
  dsimp [quadratic,fieldSynthesis]
  ring

/-- Surjectivity of the ACTUAL original basis map supplies nonvanishing
on its affine coefficient plane. This includes t=-2: q(1,1,0)=-2. -/
theorem second_nonzero (κ t : F) (u v z : Vector F) (h2 : (2:F)≠0)
    (hs : Function.Surjective (fieldSynthesis u v z)) : leadingSecond κ t u v z≠0 := by
  intro he
  have hv (i j : F) : quadratic κ t (fieldSynthesis u v z (i,j,1))=0 := by
    rw [←second_eval,he]
    simp
  obtain ⟨c,hc⟩ := hs (1,1,0)
  have hh := affine_reconstruction κ t u v z c.1 c.2.1 c.2.2
  simp only [hv,mul_zero,add_zero] at hh
  have hz : quadratic κ t (fieldSynthesis u v z c)=0 := (mul_eq_zero.mp hh).resolve_left h2
  rw [hc] at hz
  have hneg : -(2:F)=0 := by simpa [quadratic] using hz
  exact h2 (neg_eq_zero.mp hneg)

theorem wrow_nonzero (u v z : Vector F)
    (hs : Function.Surjective (fieldSynthesis u v z)) : row u.2.2 v.2.2 z.2.2≠0 := by
  intro he
  have hv (i j : F) : z.2.2+u.2.2*i+v.2.2*j=0 := by
    rw [←row_eval,he]
    simp
  have hz : z.2.2=0 := by simpa using hv 0 0
  have hu : u.2.2=0 := by simpa [hz] using hv 1 0
  have hV : v.2.2=0 := by simpa [hz] using hv 0 1
  obtain ⟨c,hc⟩ := hs (0,0,1)
  have hh := congrArg (fun y : Vector F => y.2.2) hc
  simp [fieldSynthesis,hu,hV,hz] at hh

theorem simultaneous_nonzero (κ t : F) (hκ : κ≠0) (u v z : Vector F)
    (h2 : (2:F)≠0) (hs : Function.Surjective (fieldSynthesis u v z)) :
    simultaneousLeading κ t u v z≠0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (C_ne_zero.mpr hκ) (pow_ne_zero _ (wrow_nonzero u v z hs))
  · exact second_nonzero κ t u v z h2 hs

lemma row_degree (a b c : F) : (row a b c).totalDegree≤1 := by
  have h0 : (C a*X (0:Fin 2)).totalDegree≤1 := by
    simpa using totalDegree_mul (C a) (X (0:Fin 2))
  have h1 : (C b*X (1:Fin 2)).totalDegree≤1 := by
    simpa using totalDegree_mul (C b) (X (1:Fin 2))
  exact (totalDegree_add _ _).trans (max_le
    ((totalDegree_add _ _).trans (max_le (by simp) h0)) h1)

lemma simultaneous_degree (κ t : F) (u v z : Vector F) :
    (simultaneousLeading κ t u v z).totalDegree≤4 := by
  have hw := row_degree u.2.2 v.2.2 z.2.2
  have hx := row_degree u.1 v.1 z.1
  have hz := row_degree u.2.1 v.2.1 z.2.1
  have hs : ((row u.2.2 v.2.2 z.2.2)^2).totalDegree≤2 :=
    (totalDegree_pow _ _).trans (by omega)
  have hf : (leadingFirst κ u v z).totalDegree≤2 :=
    (totalDegree_mul _ _).trans (by simpa using hs)
  have hsecond : (leadingSecond κ t u v z).totalDegree≤2 := by
    apply (totalDegree_sub _ _).trans
    apply max_le
    · exact (totalDegree_mul _ _).trans (by simpa using hs)
    · have hxy := totalDegree_mul (row u.1 v.1 z.1) (row u.2.1 v.2.1 z.2.1)
      have hh := totalDegree_mul (2: MvPolynomial (Fin 2) F)
        ((row u.1 v.1 z.1)*(row u.2.1 v.2.1 z.2.1))
      have he : 2*(row u.1 v.1 z.1)*(row u.2.1 v.2.1 z.2.1)=
          (2: MvPolynomial (Fin 2) F)*((row u.1 v.1 z.1)*(row u.2.1 v.2.1 z.2.1)) := by ring
      rw [he]
      have ht : (2: MvPolynomial (Fin 2) F).totalDegree=0 := by
        change (C (2:F): MvPolynomial (Fin 2) F).totalDegree=0
        exact totalDegree_C _
      exact hh.trans (by rw [ht]; omega)
  exact (totalDegree_mul _ _).trans (by omega)

end OriginalAffineLeadingForms318
