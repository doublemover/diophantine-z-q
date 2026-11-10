module
public import FiniteBooleanMobius318
public section
noncomputable section
namespace FiniteSelbergMinimizer318
open scoped BigOperators
open FiniteBooleanMobius318
set_option maxHeartbeats 16000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[expose] def mass (g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut] : ℝ := ∑ b,if cut b then g b else 0
@[expose] def target (g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut] (b : ι → Bool) : ℝ :=
  if cut b then sign b*g b/mass g cut else 0
@[expose] def coefficient (ν g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut] (b : ι → Bool) : ℝ := inverseTransform (target g cut) b/ν b

lemma mass_pos (g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop) [DecidablePred cut]
    (hg : ∀ b,0<g b) (hcut : cut (fun _ => false)) : 0<mass g cut := by
  apply Finset.sum_pos'
  · intro b _
    split_ifs
    · exact (hg b).le
    · exact le_rfl
  · exact ⟨(fun _ => false),Finset.mem_univ _,by simpa only [if_pos hcut] using hg (fun _ => false)⟩

/-- Normalization is constructed by the same Mobius inverse: at the
empty divisor the two signs square to one and give the ACTUAL denominator. -/
lemma coefficient_empty (ν g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut] (hν : ν (fun _ => false)=1) (hM : mass g cut≠0) :
    coefficient ν g cut (fun _ => false)=1 := by
  unfold coefficient inverseTransform
  rw [hν,div_one]
  have hs (b : ι → Bool) : mobius (fun _ => false) b*target g cut b=
      (if cut b then g b else 0)/mass g cut := by
    rw [mobius_at_empty]
    unfold target
    by_cases hb : cut b
    · rw [if_pos hb,if_pos hb]
      calc
        _ = sign b^2*g b/mass g cut := by ring
        _ = _ := by rw [sign_sq,one_mul]
    · simp only [if_neg hb,mul_zero,zero_div]
  simp_rw [hs]
  rw [←Finset.sum_div]
  exact div_self hM

lemma diagonal_coordinates (ν g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut] (hν : ∀ b,ν b≠0) (a : ι → Bool) :
    (∑ b,zeta a b*(ν b*coefficient ν g cut b))=target g cut a := by
  have hh (b : ι → Bool) : ν b*coefficient ν g cut b=inverseTransform (target g cut) b := by
    unfold coefficient
    field_simp [hν b]
  simp_rw [hh]
  exact actual_inverse _ a

lemma target_energy (g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut] (hg : ∀ b,g b≠0) (hM : mass g cut≠0) :
    (∑ b,(g b)⁻¹*(target g cut b)^2)=(mass g cut)⁻¹ := by
  have hs (b : ι → Bool) : (g b)⁻¹*(target g cut b)^2=
      (if cut b then g b else 0)/(mass g cut)^2 := by
    unfold target
    by_cases hb : cut b
    · rw [if_pos hb,if_pos hb]
      rw [div_pow,mul_pow,sign_sq,one_mul]
      field_simp [hg b,hM]
    · simp only [if_neg hb,zero_pow (by norm_num : 2≠0),mul_zero,zero_div]
  simp_rw [hs]
  rw [←Finset.sum_div]
  change mass g cut/(mass g cut)^2=(mass g cut)⁻¹
  field_simp [hM]

/-- The inverse produces support inside the SAME downward-closed
integer cutoff; no separate coefficient-support hypothesis is supplied. -/
lemma coefficient_support (ν g : (ι → Bool) → ℝ) (cut : (ι → Bool) → Prop)
    [DecidablePred cut]
    (hdown : ∀ a b,(∀ i,a i=true → b i=true) → cut b → cut a)
    (a : ι → Bool) (ha : ¬cut a) : coefficient ν g cut a=0 := by
  unfold coefficient inverseTransform
  have hs : (∑ b : ι → Bool,mobius a b*target g cut b)=0 := by
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : cut b
    · have hn : ¬∀ i,a i=true → b i=true := fun h => ha (hdown a b h hb)
      rw [mobius_zero_of_not_le a b hn,zero_mul]
    · simp only [target,if_neg hb,mul_zero]
  rw [hs,zero_div]

end FiniteSelbergMinimizer318
