module
public import PELNormalizerOctagonRealImages318
public section
namespace PELNormalizerOctagonWholeImages318
open PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318
open PELNormalizerOctagonAffine318 PELNormalizerOctagonVertices318 PELNormalizerOctagonStrata318
open PELNormalizerOctagonMinimum318 PELNormalizerOctagonStrict318
open PELNormalizerOctagonRealImages318 PELPositiveNormalizerKlein318
open NormalizerVertexEnergyMinimum318
set_option maxHeartbeats 5000000

/-- Whole original-coordinate equality classifier: the two independent
signs on the boundary become the SAME sign in the strict interior. -/
theorem whole_integer_rows (i : Fin 16) (x : Coordinates)
    (hn : integerNorm x=(allowedNorm i:ℤ)) (P : ℝ × ℝ)
    (hP : inequalities P.1 P.2) (he : realDen (embed x) P.1 P.2=(allowedNorm i:ℝ)) :
    ∃ a b : Bool,
      realRow (embed x) 0 P.1 P.2=(allowedNorm i:ℝ)*signR a P.1 ∧
      realRow (embed x) 1 P.1 P.2=(allowedNorm i:ℝ)*signR b P.2 ∧
      (strict P → a=b) := by
  by_cases hs : strict P
  · have hx := integer_strict_equality i x hn P hs he
    have hN : (allowedNorm i:ℝ)=(integerNorm x:ℝ) := by exact_mod_cast hn.symm
    rw [hN]
    rcases hx with rfl | rfl | rfl | rfl
    · refine ⟨true,true,?_,?_,fun _ => rfl⟩ <;>
        norm_num [realRow,PELQuaternionKleinAction318.matrix,embed,integerNorm,signR]
    · refine ⟨true,true,?_,?_,fun _ => rfl⟩ <;>
        norm_num [realRow,PELQuaternionKleinAction318.matrix,embed,integerNorm,signR]
    · refine ⟨false,false,?_,?_,fun _ => rfl⟩ <;>
        norm_num [realRow,PELQuaternionKleinAction318.matrix,embed,integerNorm,signR] <;> ring
    · refine ⟨false,false,?_,?_,fun _ => rfl⟩ <;>
        norm_num [realRow,PELQuaternionKleinAction318.matrix,embed,integerNorm,signR] <;> ring
  · obtain hstrict | ⟨v,s,hs0,hs1,hPs⟩ := closed_side_or_strict P hP
    · exact (hs hstrict).elim
    have hab : ∃ a b : Bool,
        realRow (embed x) 0 P.1 P.2=(allowedNorm i:ℝ)*signR a P.1 ∧
        realRow (embed x) 1 P.1 P.2=(allowedNorm i:ℝ)*signR b P.2 := by
      by_cases h0 : s=0
      · subst s
        have hPv : P=(((vertex v).1:ℝ),((vertex v).2:ℝ)) := by simpa [mix] using hPs
        rw [hPv] at he ⊢
        exact integer_vertex_rows i x hn v he
      by_cases h1 : s=1
      · subst s
        have hPv : P=(((vertex (PELNormalizerOctagonImageCertificate318.next v)).1:ℝ),
            ((vertex (PELNormalizerOctagonImageCertificate318.next v)).2:ℝ)) := by simpa [mix] using hPs
        rw [hPv] at he ⊢
        exact integer_vertex_rows i x hn _ he
      · rw [hPs] at he ⊢
        exact integer_open_side_rows i x hn v s
          (lt_of_le_of_ne hs0 h0.symm) (lt_of_le_of_ne hs1 h1) he
    obtain ⟨a,b,hA,hY⟩ := hab
    exact ⟨a,b,hA,hY,fun h => (hs h).elim⟩
end PELNormalizerOctagonWholeImages318
