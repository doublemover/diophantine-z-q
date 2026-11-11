module
public import ActualOriginalEliminantNonzero318
public section
noncomputable section
namespace ActualQuarticOffsetDegree318
open MvPolynomial TernaryQuadraticLineCover318 ActualQuarticOffsetPolynomial318
open OriginalOffsetEliminant318
set_option maxHeartbeats 10000000

private lemma add_degree {a b : MvPolynomial (Fin 2) ℤ} {n : ℕ}
    (ha : a.totalDegree≤n) (hb : b.totalDegree≤n) : (a+b).totalDegree≤n :=
  (totalDegree_add _ _).trans (max_le ha hb)
private lemma sub_degree {a b : MvPolynomial (Fin 2) ℤ} {n : ℕ}
    (ha : a.totalDegree≤n) (hb : b.totalDegree≤n) : (a-b).totalDegree≤n :=
  (totalDegree_sub _ _).trans (max_le ha hb)
private lemma mul_degree {a b : MvPolynomial (Fin 2) ℤ} {m n : ℕ}
    (ha : a.totalDegree≤m) (hb : b.totalDegree≤n) : (a*b).totalDegree≤m+n :=
  (totalDegree_mul _ _).trans (Nat.add_le_add ha hb)
private lemma pow_degree {a : MvPolynomial (Fin 2) ℤ} {m : ℕ}
    (ha : a.totalDegree≤m) (n : ℕ) : (a^n).totalDegree≤m*n := by
  simpa only [Nat.mul_comm] using (totalDegree_pow a n).trans (Nat.mul_le_mul_left n ha)
private lemma const_degree (a : ℤ) : (C a : MvPolynomial (Fin 2) ℤ).totalDegree≤0 := by simp

lemma component_degrees (κ t : ℤ) (u v d : Vector ℤ) :
    (R2 κ d).totalDegree≤0 ∧ (R1 κ u v d).totalDegree≤1 ∧
    (R0 κ t u v).totalDegree≤2 ∧ (S u v).totalDegree≤1 := by
  have hx := linear_degree u.1 v.1
  have hz := linear_degree u.2.1 v.2.1
  have hw := linear_degree u.2.2 v.2.2
  refine ⟨const_degree _,?_,?_,add_degree hx hz⟩
  · exact sub_degree (sub_degree (by simpa using mul_degree (const_degree _) hw)
      (by simpa using mul_degree (const_degree _) hx))
      (by simpa using mul_degree (const_degree _) hz)
  · exact add_degree (sub_degree (by simpa using mul_degree (const_degree _) (pow_degree hw 2))
      (by simpa using mul_degree hx hz)) (by simpa using (const_degree (t^2+2*t)).trans (by omega))

lemma quartic_degrees (κ t : ℤ) (u v d : Vector ℤ) :
    (E4 κ u v d).totalDegree≤0 ∧ (E3 κ u v d).totalDegree≤1 ∧
    (E2 κ t u v d).totalDegree≤2 ∧ (E1 κ t u v d).totalDegree≤3 ∧
    (E0 κ t u v d).totalDegree≤4 := by
  obtain ⟨h2,h1,h0,hs⟩ := component_degrees κ t u v d
  have hc := const_degree (2:ℤ)
  refine ⟨by simpa [E4] using pow_degree h2 2,?_,?_,?_,?_⟩
  · simpa [E3] using mul_degree (mul_degree hc h2) h1
  · apply add_degree
    · exact add_degree (by simpa [E2] using pow_degree h1 2)
        (by simpa using mul_degree (mul_degree hc h2) h0)
    · exact (const_degree _).trans (by omega)
  · exact add_degree (by simpa using mul_degree (mul_degree hc h1) h0)
      ((by simpa using mul_degree (const_degree _) hs :
        (C (2*t^2*(d.1+d.2.1))*S u v).totalDegree≤1).trans (by omega))
  · exact add_degree (by simpa using pow_degree h0 2)
      ((by simpa using mul_degree (const_degree _) (pow_degree hs 2) :
        (C (t^2)*(S u v)^2).totalDegree≤2).trans (by omega))

/-- Weighted coefficient grading of the genuine quadratic/quartic
pseudo-resultant. It gives degree8, not a degree inherited from old D. -/
lemma eliminant_degree (a b c e f g h i : MvPolynomial (Fin 2) ℤ)
    (ha : a.totalDegree≤0) (hb : b.totalDegree≤1) (hc : c.totalDegree≤2)
    (he : e.totalDegree≤0) (hf : f.totalDegree≤1) (hg : g.totalDegree≤2)
    (hh : h.totalDegree≤3) (hi : i.totalDegree≤4) :
    (ActualQuadraticQuarticEliminant318.eliminant a b c e f g h i).totalDegree≤8 := by
  let L := ActualQuadraticQuarticEliminant318.linearTerm a b c e f g h i
  let M := ActualQuadraticQuarticEliminant318.constantTerm a b c e f g h i
  have hL : L.totalDegree≤3 := by
    have hneg : (-b^3).totalDegree≤3 := by simpa using pow_degree hb 3
    have h2abc : ((2: MvPolynomial (Fin 2) ℤ)*a*b*c).totalDegree≤3 := by
      simpa using mul_degree (mul_degree (mul_degree (const_degree 2) ha) hb) hc
    have hfirst : (e*(-b^3+2*a*b*c)).totalDegree≤3 := by
      simpa using mul_degree he (add_degree hneg h2abc)
    have hmid : (f*a*(b^2-a*c)).totalDegree≤3 := by
      simpa using mul_degree (mul_degree hf ha)
        (sub_degree (by simpa using pow_degree hb 2) (by simpa using mul_degree ha hc))
    have hthird : (g*a^2*b).totalDegree≤3 := by simpa using mul_degree (mul_degree hg (pow_degree ha 2)) hb
    have hlast : (h*a^3).totalDegree≤3 := by simpa using mul_degree hh (pow_degree ha 3)
    exact add_degree (sub_degree (add_degree hfirst hmid) hthird) hlast
  have hM : M.totalDegree≤4 := by
    have hneg : (-b^2*c).totalDegree≤4 := by simpa using mul_degree (pow_degree hb 2) hc
    have hfirst : (e*(-b^2*c+a*c^2)).totalDegree≤4 := by
      simpa using mul_degree he (add_degree hneg (by simpa using mul_degree ha (pow_degree hc 2)))
    have hmid : (f*a*b*c).totalDegree≤4 := by simpa using mul_degree (mul_degree (mul_degree hf ha) hb) hc
    have hthird : (g*a^2*c).totalDegree≤4 := by simpa using mul_degree (mul_degree hg (pow_degree ha 2)) hc
    have hlast : (i*a^3).totalDegree≤4 := by simpa using mul_degree hi (pow_degree ha 3)
    exact add_degree (sub_degree (add_degree hfirst hmid) hthird) hlast
  exact add_degree (sub_degree (by simpa using mul_degree ha (pow_degree hM 2))
    (by simpa using mul_degree (mul_degree hb hL) hM))
    (by simpa using mul_degree hc (pow_degree hL 2))

lemma actual_degree (κ t : ℤ) (u v d : Vector ℤ) :
    (ActualQuarticOffsetPolynomial318.polynomial κ t u v d).totalDegree≤8 := by
  obtain ⟨h4,h3,h2,h1,h0⟩ := quartic_degrees κ t u v d
  exact eliminant_degree _ _ _ _ _ _ _ _ (const_degree _) (eB_degree true κ t u v d)
    (eC_degree true κ t u v) h4 h3 h2 h1 h0

end ActualQuarticOffsetDegree318
