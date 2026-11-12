module
public import PELNormalizerOctagonReduction318
public section
namespace NormalizerVertexEnergyEquality318
open NormalizerVertexEnergyBounds318 NormalizerVertexEnergyMinimum318
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
@[expose] def equalityRow : Fin 2 → Fin 16 → Fin 4 → ℤ := ![
  ![![2,0,0,0],![-2,0,0,0],![15,0,-3,-2],![-15,0,3,2],![5,0,-1,0],![-5,0,1,0],![14,-2,-14,0],![-14,2,14,0],![-30,-1,0,5],![30,1,0,-5],![0,-1,0,1],![0,1,0,-1],![0,-5,-28,5],![0,5,28,-5],![0,-2,0,0],![0,2,0,0]],
  ![![2,0,0,0],![-2,0,0,0],![14,0,-2,-2],![-14,0,2,2],![14,0,0,-2],![-14,0,0,2],![14,-2,-14,0],![-14,2,14,0],![-30,-1,0,5],![30,1,0,-5],![0,-2,-12,0],![0,2,12,0],![0,-7,-42,5],![0,7,42,-5],![0,-2,0,0],![0,2,0,0]]]

/-- Inclusive radii are derived before the equality enumeration. -/
theorem bounds_of_equal (k : Fin 2) (N : ℕ) (s r c d : ℤ)
    (h : energy k s r c d=threshold k N) :
    r.natAbs≤radiusR k N ∧ c.natAbs≤radiusC k N ∧ d.natAbs≤radiusD k N := by
  fin_cases k
  · have ⟨hr,hc,hd⟩ := energy0_bounds s r c d
    simp only [energy,threshold,if_pos rfl] at h
    refine ⟨?_,?_,?_⟩
    · exact natAbs_bound r 56 (20*N) (by decide) (by push_cast; linarith)
    · exact natAbs_bound c 4 (60*N) (by decide) (by push_cast; linarith)
    · exact natAbs_bound d 56 (100*N) (by decide) (by push_cast; linarith)
  · have ⟨hr,hc,hd⟩ := energy1_bounds s r c d
    norm_num only [energy,threshold] at h
    refine ⟨?_,?_,?_⟩
    · exact natAbs_bound r 60 (28*N) (by decide) (by push_cast; linarith)
    · exact natAbs_bound c 10 (196*N) (by decide) (by push_cast; linarith)
    · exact natAbs_bound d 12 (28*N) (by decide) (by push_cast; linarith)

theorem bounded_equality (i : Fin 16) (k : Fin 2)
    (r : Fin (radiusR k (allowedNorm i)+1))
    (c : Fin (radiusC k (allowedNorm i)+1))
    (d : Fin (radiusD k (allowedNorm i)+1)) (sr sc sd ss : Bool) :
    let R := sign sr (r.val:ℤ)
    let C := sign sc (c.val:ℤ)
    let D := sign sd (d.val:ℤ)
    let S := sign ss (root (allowedNorm i) R C D)
    S^2+210*R^2-5*C^2-42*D^2=4*(allowedNorm i:ℤ) →
      energy k S R C D=threshold k (allowedNorm i) →
        ∃ j : Fin 16,equalityRow k j=![S,R,C,D] := by
  revert r c d sr sc sd ss
  fin_cases i <;> fin_cases k <;> decide

/-- Every whole-lattice equality case is one of the displayed rows. -/
theorem whole_integer_equality (i : Fin 16) (k : Fin 2) (s r c d : ℤ)
    (hn : s^2+210*r^2-5*c^2-42*d^2=4*(allowedNorm i:ℤ))
    (he : energy k s r c d=threshold k (allowedNorm i)) :
    ∃ j : Fin 16,equalityRow k j=![s,r,c,d] := by
  obtain ⟨hr,hc,hd⟩ := bounds_of_equal k (allowedNorm i) s r c d he
  obtain ⟨sr,hsr⟩ := sign_choice r
  obtain ⟨sc,hsc⟩ := sign_choice c
  obtain ⟨sd,hsd⟩ := sign_choice d
  obtain ⟨ss,hss⟩ := sign_choice s
  have hf := root_forced (allowedNorm i) s r c d hn
  have hb := bounded_equality i k ⟨r.natAbs,by omega⟩ ⟨c.natAbs,by omega⟩
    ⟨d.natAbs,by omega⟩ sr sc sd ss
  simp only [hsr,hsc,hsd,hf,hss] at hb
  exact hb hn he
end NormalizerVertexEnergyEquality318
