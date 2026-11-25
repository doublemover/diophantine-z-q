module
public import OriginalAffineReesBlowup318
public section
noncomputable section

namespace OriginalReesDegreeOneCover318

open AlgebraicGeometry Polynomial
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318

universe u v
variable {R : Type u} [CommRing R] (I : Ideal R)
variable (ι : Type v) (a : ι → I)

abbrev gens (i : ι) : Rees I := generator I (a i).val (a i).property

variable (hspan : Ideal.span (Set.range (fun i => (a i).val)) = I)
include hspan

private theorem one_mem_span {r : R} (hr : r ∈ I) :
    generator I r hr ∈ Ideal.span (Set.range (gens I ι a)) := by
  let J := Ideal.span (Set.range (gens I ι a))
  let S := Set.range (fun i => (a i).val)
  have hs : Submodule.span R S = I := hspan
  have h : r ∈ Submodule.span R S := hs.symm ▸ hr
  exact Submodule.span_induction
    (p:=fun b hb => generator I b (hs ▸ hb) ∈ J)
    (by
      intro b hb
      obtain ⟨i,rfl⟩ := hb
      exact Ideal.subset_span ⟨i,rfl⟩)
    (by
      convert Ideal.zero_mem J using 1
      apply Subtype.ext
      exact monomial_zero_right _)
    (by
      intro b c hb hc h₁ h₂
      have he : generator I (b+c) (hs ▸ Submodule.add_mem _ hb hc) =
          generator I b (hs ▸ hb) + generator I c (hs ▸ hc) := by
        apply Subtype.ext
        change monomial 1 (b+c) = monomial 1 b + monomial 1 c
        exact map_add _ _ _
      rw [he]
      exact Ideal.add_mem J h₁ h₂)
    (by
      intro t b hb h₁
      have he : generator I (t • b) (hs ▸ Submodule.smul_mem _ _ hb) =
          algebraMap R (Rees I) t * generator I b (hs ▸ hb) := by
        apply Subtype.ext
        change monomial 1 (t*b) = C t * monomial 1 b
        exact C_mul_monomial.symm
      rw [he]
      exact Ideal.mul_mem_left _ _ h₁) h

private theorem pos_monomial_mem (n : ℕ) (r : R) (hr : r ∈ I^(n+1)) :
    (homogeneous I (n+1) r hr).val ∈ Ideal.span (Set.range (gens I ι a)) := by
  let J := Ideal.span (Set.range (gens I ι a))
  have h : r ∈ I * I^n := by rw [← pow_succ']; exact hr
  exact Submodule.mul_induction_on'
    (C:=fun t ht => (homogeneous I (n+1) t (by rw [pow_succ']; exact ht)).val ∈ J)
    (by
      intro b hb c hc
      have he : (homogeneous I (n+1) (b*c) (by rw [pow_succ']; exact Ideal.mul_mem_mul hb hc)).val =
          generator I b hb * (homogeneous I n c hc).val := by
        apply Subtype.ext
        change monomial (n+1) (b*c) = monomial 1 b * monomial n c
        rw [monomial_mul_monomial, Nat.add_comm 1 n]
      rw [he]
      exact Ideal.mul_mem_right _ _ (one_mem_span I ι a hspan hb))
    (by
      intro b hb c hc h₁ h₂
      have he : (homogeneous I (n+1) (b+c) (by rw [pow_succ']; exact Ideal.add_mem _ hb hc)).val =
          (homogeneous I (n+1) b (by rw [pow_succ']; exact hb)).val +
          (homogeneous I (n+1) c (by rw [pow_succ']; exact hc)).val := by
        apply Subtype.ext
        change monomial (n+1) (b+c) = monomial (n+1) b + monomial (n+1) c
        exact map_add _ _ _
      rw [he]
      exact Ideal.add_mem J h₁ h₂) h

variable {ι} in
/-- Actual ideal of positive degree in the real Rees algebra is
covered by the chosen honest degree-one generators a_i T. -/
theorem span_covers :
    (HomogeneousIdeal.irrelevant (grade I)).toIdeal ≤ Ideal.span (Set.range (gens I ι a)) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (grade I)).2
  intro n hn f hf
  change f ∈ grade I n at hf
  change f ∈ Ideal.span (Set.range (gens I ι a))
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hread : f = (homogeneous I (m+1) (f.val.coeff (m+1)) (f.property (m+1))).val := by
    apply Subtype.ext
    exact homogeneous_value I hf
  rw [hread]
  exact pos_monomial_mem I ι a hspan m _ _

end OriginalReesDegreeOneCover318

#print axioms OriginalReesDegreeOneCover318.span_covers
