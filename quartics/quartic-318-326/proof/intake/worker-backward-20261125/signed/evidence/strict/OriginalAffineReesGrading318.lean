module
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public section
noncomputable section

namespace OriginalAffineReesGrading318

open Polynomial DirectSum
open scoped DirectSum

universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

abbrev Rees := reesAlgebra I

/-- Degree n is the degree-n monomial part of the genuine pinned
reesAlgebra I ⊆ R[X], not an incidence quotient or an assumed grading. -/
@[expose] def grade (n : ℕ) : Submodule R (Rees I) where
  carrier := {f | ∀ m, m ≠ n → f.val.coeff m = 0}
  zero_mem' := by
    intro m _
    exact Polynomial.coeff_zero m
  add_mem' := by
    intro f g hf hg m hm
    change (f.val + g.val).coeff m = 0
    rw [coeff_add, hf m hm, hg m hm, zero_add]
  smul_mem' := by
    intro a f hf m hm
    change ((↑(a • f) : R[X]).coeff m) = 0
    rw [Subalgebra.coe_smul, Polynomial.coeff_smul, hf m hm, smul_zero]

@[expose] def homogeneous (n : ℕ) (a : R) (ha : a ∈ I^n) : grade I n :=
  ⟨⟨monomial n a, reesAlgebra.monomial_mem.mpr ha⟩, by
    intro m hm
    simp [coeff_monomial, Ne.symm hm]⟩

theorem homogeneous_value {n : ℕ} {f : Rees I} (hf : f ∈ grade I n) :
    f.val = monomial n (f.val.coeff n) := by
  apply Polynomial.ext
  intro m
  by_cases h : m = n
  · subst m
    exact (coeff_monomial_same _ _).symm
  · have hz : f.val.coeff m = 0 := hf m h
    simp [coeff_monomial, Ne.symm h, hz]

instance gradedMonoid : SetLike.GradedMonoid (grade I) where
  one_mem := by
    intro m hm
    change (1 : R[X]).coeff m = 0
    simp [coeff_one, hm]
  mul_mem := by
    intro n m f g hf hg j hj
    change (f.val * g.val).coeff j = 0
    rw [homogeneous_value I hf, homogeneous_value I hg, monomial_mul_monomial]
    simp [coeff_monomial, Ne.symm hj]

@[expose] def parts (f : Rees I) : ⨁ n, grade I n :=
  ∑ n ∈ f.val.support, DirectSum.of (fun n => ↥(grade I n)) n
    (homogeneous I n (f.val.coeff n) (f.property n))

theorem parts_apply (f : Rees I) (n : ℕ) :
    parts I f n = homogeneous I n (f.val.coeff n) (f.property n) := by
  classical
  rw [parts, DFinsupp.finsetSum_apply, Finset.sum_eq_single n]
  · exact DirectSum.of_eq_same _ _
  · intro b _ hb
    exact DirectSum.of_eq_of_ne _ _ _ (Ne.symm hb)
  · intro hn
    have hz := Polynomial.notMem_support_iff.mp hn
    rw [DirectSum.of_eq_same]
    apply Subtype.ext
    apply Subtype.ext
    change monomial n (f.val.coeff n) = 0
    rw [hz, monomial_zero_right]

@[expose] def partsAdd : Rees I →+ ⨁ n, grade I n where
  toFun := parts I
  map_zero' := by
    ext n : 1
    rw [parts_apply]
    apply Subtype.ext
    apply Subtype.ext
    change monomial n ((0 : R[X]).coeff n) = 0
    rw [coeff_zero, monomial_zero_right]
  map_add' := by
    intro f g
    ext n : 1
    change parts I (f + g) n = parts I f n + parts I g n
    rw [parts_apply, parts_apply, parts_apply]
    apply Subtype.ext
    apply Subtype.ext
    change monomial n ((f.val + g.val).coeff n) =
      monomial n (f.val.coeff n) + monomial n (g.val.coeff n)
    rw [coeff_add, map_add]

instance gradedRing : GradedRing (grade I) := by
  classical
  have hl : (DirectSum.coeAddMonoidHom (grade I)).comp (partsAdd I) =
      AddMonoidHom.id (Rees I) := by
    apply AddMonoidHom.ext
    intro f
    change DirectSum.coeAddMonoidHom (grade I) (parts I f) = f
    rw [parts, map_sum]
    calc
      _ = ∑ n ∈ f.val.support, (homogeneous I n (f.val.coeff n) (f.property n)).val := by
        simp only [DirectSum.coeAddMonoidHom_of]
      _ = ∑ n ∈ f.val.support,
          (⟨monomial n (f.val.coeff n), reesAlgebra.monomial_coeff_mem f n⟩ : Rees I) := by
        apply Finset.sum_congr rfl
        intro n _
        apply Subtype.ext
        rfl
      _ = f := (reesAlgebra.as_sum_support f).symm
  have hr : (partsAdd I).comp (DirectSum.coeAddMonoidHom (grade I)) =
      AddMonoidHom.id (⨁ n, grade I n) := by
    apply DirectSum.addHom_ext
    intro n x
    change parts I (DirectSum.coeAddMonoidHom (grade I) (DirectSum.of _ n x)) =
      DirectSum.of _ n x
    rw [DirectSum.coeAddMonoidHom_of]
    ext j : 1
    rw [parts_apply]
    by_cases h : j = n
    · subst j
      rw [DirectSum.of_eq_same]
      apply Subtype.ext
      apply Subtype.ext
      exact (homogeneous_value I x.property).symm
    · rw [DirectSum.of_eq_of_ne _ _ _ h]
      apply Subtype.ext
      apply Subtype.ext
      change monomial j (x.val.val.coeff j) = 0
      rw [show x.val.val.coeff j = 0 from x.property j h, monomial_zero_right]
  refine
    { toGradedMonoid := gradedMonoid I
      decompose' := parts I
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    exact DFunLike.congr_fun hl z
  · intro z
    exact DFunLike.congr_fun hr z

@[expose] def constantRead : (grade I 0) →+* R :=
  Polynomial.constantCoeff.comp ((Subalgebra.val (reesAlgebra I)).toRingHom.comp
    (SetLike.GradeZero.subring (grade I)).subtype)

/-- The actual base is degree zero in this grading. -/
@[expose] def gradeZero : R ≃+* grade I 0 :=
  RingEquiv.ofRingHom (algebraMap R (grade I 0)) (constantRead I) (by
    apply RingHom.ext
    intro f
    apply Subtype.ext
    apply Subtype.ext
    change C (f.val.val.coeff 0) = f.val.val
    rw [← monomial_zero_left]
    exact (homogeneous_value I f.property).symm) (by
    apply RingHom.ext
    intro a
    change (C a).coeff 0 = a
    rw [coeff_C_zero])

theorem finiteType_of_fg (hI : I.FG) : Algebra.FiniteType (grade I 0) (Rees I) := by
  let : Algebra.FiniteType R (Rees I) :=
    ⟨(reesAlgebra I).fg_top.mpr (reesAlgebra.fg hI)⟩
  obtain ⟨s,hs⟩ := (inferInstance : Algebra.FiniteType R (Rees I)).out
  let J := Algebra.adjoin (grade I 0) (s : Set (Rees I))
  refine ⟨⟨s, eq_top_iff.mpr ?_⟩⟩
  intro z _
  change z ∈ J
  have hz : z ∈ Algebra.adjoin R (s : Set (Rees I)) := by rw [hs]; trivial
  exact Algebra.adjoin_induction (p:=fun x _ => x ∈ J)
    (fun _ hx => Algebra.subset_adjoin hx)
    (fun t => by
      have hh : algebraMap (grade I 0) (Rees I) (gradeZero I t) = algebraMap R (Rees I) t :=
        SetLike.GradeZero.coe_algebraMap (grade I) t
      rw [← hh]
      exact J.algebraMap_mem _)
    (fun _ _ _ _ hx hy => J.add_mem hx hy)
    (fun _ _ _ _ hx hy => J.mul_mem hx hy) hz

end OriginalAffineReesGrading318

#print axioms OriginalAffineReesGrading318.gradedRing
#print axioms OriginalAffineReesGrading318.gradeZero
#print axioms OriginalAffineReesGrading318.finiteType_of_fg
