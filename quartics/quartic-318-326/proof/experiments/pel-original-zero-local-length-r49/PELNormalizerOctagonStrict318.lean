module
public import PELNormalizerOctagonStrata318
public section
namespace PELNormalizerOctagonStrict318
open PELNormalizerOctagonAffine318 PELNormalizerOctagonVertices318 PELNormalizerOctagonStrata318
open PELNormalizerOctagonMinimum318 PELNormalizerOctagonImageCertificate318
open PELPrincipalOrderCoordinates318 PELDirichletOriginalUnits318 NormalizerVertexEnergyMinimum318
set_option maxHeartbeats 4000000

theorem radial_extension (P : ℝ × ℝ) (h : strict P) :
    ∃ t : ℝ,1<t ∧ inequalities (t*P.1) (t*P.2) := by
  let a : Fin 8 → ℝ := ![-P.2,P.2,-P.1,P.1,-P.1-7*P.2,P.1+7*P.2,-P.1+7*P.2,P.1-7*P.2]
  let c : Fin 8 → ℝ := ![1,1,30,30,35,35,35,35]
  have hs (i : Fin 8) (_ : i∈(Finset.univ : Finset (Fin 8))) : a i<c i := by
    obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := h
    fin_cases i <;> norm_num [a,c] <;> linarith
  obtain ⟨δ,hδ,hd⟩ := FiniteStrictRadialExtension318.finite_slack Finset.univ a c hs
  refine ⟨1+δ,by linarith,?_⟩
  have h0 := hd 0 (Finset.mem_univ _) δ hδ.le le_rfl
  have h1 := hd 1 (Finset.mem_univ _) δ hδ.le le_rfl
  have h2 := hd 2 (Finset.mem_univ _) δ hδ.le le_rfl
  have h3 := hd 3 (Finset.mem_univ _) δ hδ.le le_rfl
  have h4 := hd 4 (Finset.mem_univ _) δ hδ.le le_rfl
  have h5 := hd 5 (Finset.mem_univ _) δ hδ.le le_rfl
  have h6 := hd 6 (Finset.mem_univ _) δ hδ.le le_rfl
  have h7 := hd 7 (Finset.mem_univ _) δ hδ.le le_rfl
  norm_num [a,c] at h0 h1 h2 h3 h4 h5 h6 h7
  unfold inequalities
  exact ⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,
    by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩

theorem affine_origin_equality (N p q c : ℝ) (P : ℝ × ℝ) (hP : strict P)
    (hm : ∀ A Y : ℝ,inequalities A Y → N≤p*A+q*Y+c)
    (he : p*P.1+q*P.2+c=N) : c=N := by
  obtain ⟨t,ht,hT⟩ := radial_extension P hP
  have hscale := hm (t*P.1) (t*P.2) hT
  have hzero := hm 0 0 (by norm_num [inequalities])
  have hid : p*(t*P.1)+q*(t*P.2)+c=t*(p*P.1+q*P.2+c)+(1-t)*c := by ring
  rw [hid,he] at hscale
  norm_num at hzero
  nlinarith

/-- Every affine minimum attained in the strict interior is constant at
all eight vertices. Antipodal points, not assumed polygon symmetry of a
finite normalizer table, force the two affine coefficients to vanish. -/
theorem affine_all_vertices (N p q c : ℝ) (P : ℝ × ℝ) (hP : strict P)
    (hm : ∀ A Y : ℝ,inequalities A Y → N≤p*A+q*Y+c)
    (he : p*P.1+q*P.2+c=N) :
    ∀ v : Fin 8,p*((vertex v).1:ℝ)+q*((vertex v).2:ℝ)+c=N := by
  have hc := affine_origin_equality N p q c P hP hm he
  intro v
  have hp : inequalities ((vertex v).1:ℝ) ((vertex v).2:ℝ) := by
    fin_cases v <;> norm_num [vertex,inequalities]
  have hn : inequalities (-((vertex v).1:ℝ)) (-((vertex v).2:ℝ)) := by
    fin_cases v <;> norm_num [vertex,inequalities]
  have hplus := hm _ _ hp
  have hminus := hm _ _ hn
  linarith

/-- The strict original octagon permits exactly identity/central-sign and
center210/its sign as primitive integer equality vectors. The210 isotropy
is retained rather than falsely proving singleton full-group interiors. -/
theorem integer_strict_equality (i : Fin 16) (x : Coordinates)
    (hn : integerNorm x=(allowedNorm i:ℤ)) (P : ℝ × ℝ) (hP : strict P)
    (he : realDen (embed x) P.1 P.2=(allowedNorm i:ℝ)) :
    x=![1,0,0,0] ∨ x=![-1,0,0,0] ∨ x=![0,1,0,0] ∨ x=![0,-1,0,0] := by
  apply all_vertex_coordinates i x hn
  have hv := affine_all_vertices (allowedNorm i:ℝ)
    ((PELQuaternionKleinAction318.matrix (embed x) 2 0:ℚ):ℝ)
    ((PELQuaternionKleinAction318.matrix (embed x) 2 1:ℚ):ℝ)
    ((PELQuaternionKleinAction318.matrix (embed x) 2 2:ℚ):ℝ) P hP
    (fun A Y h => integer_whole_octagon i x hn A Y h) he
  intro v
  have h := hv v
  change realDen (embed x) (vertex v).1 (vertex v).2=(allowedNorm i:ℝ) at h
  rw [realDen_cast] at h
  exact_mod_cast h
end PELNormalizerOctagonStrict318
