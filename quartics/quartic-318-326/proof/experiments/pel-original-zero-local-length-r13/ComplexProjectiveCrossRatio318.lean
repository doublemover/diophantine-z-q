module
public import ComplexSphereFourPointNormalization318
public section
noncomputable section
namespace ComplexProjectiveCrossRatio318
open scoped OnePoint

/-- Homogeneous determinants keep infinity in the SAME formula. -/
@[expose] def bracket (u v : ℂ × ℂ) : ℂ := u.1*v.2-u.2*v.1
@[expose] def scale (s : ℂ) (u : ℂ × ℂ) : ℂ × ℂ := (s*u.1,s*u.2)
@[expose] def matrix (a b c d : ℂ) (u : ℂ × ℂ) : ℂ × ℂ :=
  (a*u.1+b*u.2,c*u.1+d*u.2)
@[expose] def ratio (v : Fin 4 → ℂ × ℂ) : ℂ :=
  (bracket (v 0) (v 2)*bracket (v 1) (v 3))/
    (bracket (v 0) (v 3)*bracket (v 1) (v 2))

lemma bracket_scale (s t : ℂ) (u v : ℂ × ℂ) :
    bracket (scale s u) (scale t v)=(s*t)*bracket u v := by
  dsimp [bracket,scale]
  ring
lemma bracket_matrix (a b c d : ℂ) (u v : ℂ × ℂ) :
    bracket (matrix a b c d u) (matrix a b c d v)=
      (a*d-b*c)*bracket u v := by
  dsimp [bracket,matrix]
  ring

/-- Independent changes of homogeneous representatives cancel exactly;
no assumption about a finite affine chart is used. -/
theorem ratio_scale (v : Fin 4 → ℂ × ℂ) (s : Fin 4 → ℂ)
    (hs : ∀ i, s i≠0) : ratio (fun i=>scale (s i) (v i))=ratio v := by
  unfold ratio
  simp only [bracket_scale]
  have hn : ((s 0*s 2)*bracket (v 0) (v 2))*((s 1*s 3)*bracket (v 1) (v 3))=
      (s 0*s 1*s 2*s 3)*(bracket (v 0) (v 2)*bracket (v 1) (v 3)) := by ring
  have hd : ((s 0*s 3)*bracket (v 0) (v 3))*((s 1*s 2)*bracket (v 1) (v 2))=
      (s 0*s 1*s 2*s 3)*(bracket (v 0) (v 3)*bracket (v 1) (v 2)) := by ring
  rw [hn,hd]
  exact mul_div_mul_left _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (hs 0) (hs 1)) (hs 2)) (hs 3))

/-- Actual invertible linear coordinate changes preserve the ratio. -/
theorem ratio_matrix (v : Fin 4 → ℂ × ℂ) (a b c d : ℂ)
    (hdet : a*d-b*c≠0) : ratio (fun i=>matrix a b c d (v i))=ratio v := by
  unfold ratio
  simp only [bracket_matrix]
  have hn : ((a*d-b*c)*bracket (v 0) (v 2))*((a*d-b*c)*bracket (v 1) (v 3))=
      (a*d-b*c)^2*(bracket (v 0) (v 2)*bracket (v 1) (v 3)) := by ring
  have hd : ((a*d-b*c)*bracket (v 0) (v 3))*((a*d-b*c)*bracket (v 1) (v 2))=
      (a*d-b*c)^2*(bracket (v 0) (v 3)*bracket (v 1) (v 2)) := by ring
  rw [hn,hd]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hdet)

@[expose] def lift (p : OnePoint ℂ) : ℂ × ℂ := p.elim (1,0) (fun z=>(z,1))
@[expose] def crossRatio (p : Fin 4 → OnePoint ℂ) : ℂ := ratio (fun i=>lift (p i))

/-- A coordinate change is used only after its action on every original
sphere point has an actual nonzero homogeneous representative. -/
theorem crossRatio_of_action (f : OnePoint ℂ → OnePoint ℂ)
    (a b c d : ℂ) (hdet : a*d-b*c≠0)
    (hf : ∀ p, ∃ s : ℂ, s≠0 ∧ lift (f p)=scale s (matrix a b c d (lift p)))
    (p : Fin 4 → OnePoint ℂ) : crossRatio (fun i=>f (p i))=crossRatio p := by
  choose s hs he using hf
  change ratio (fun i=>lift (f (p i)))=ratio (fun i=>lift (p i))
  simp_rw [he]
  rw [ratio_scale _ _ (fun i=>hs (p i)),ratio_matrix _ _ _ _ _ hdet]

lemma crossRatio_normalized (t : ℂ) : crossRatio ![∞,(0:ℂ),(1:ℂ),(t:ℂ)]=t := by
  simp [crossRatio,ratio,bracket,lift]
end ComplexProjectiveCrossRatio318
