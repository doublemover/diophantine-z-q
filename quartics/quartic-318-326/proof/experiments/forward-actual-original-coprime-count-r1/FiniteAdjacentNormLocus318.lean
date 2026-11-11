module
public import FiniteFiveQuadricCount318
public section
noncomputable section
namespace FiniteAdjacentNormLocus318
open FiniteFiveQuadricCount318
set_option maxHeartbeats 1000000
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

@[expose] def Bad (κ ε η : F) := {z : Quadric κ //
  (z.1.1.1+ε)^2+z.1.1.2^2=0 ∧ (z.1.2.1.1+η)^2+z.1.2.1.2^2=0}

/-- The adjacent unit shifts exclude the original zero vector. -/
lemma bad_nonzero (κ ε η : F) (hε : ε^2=1) (z : Bad κ ε η) :
    z.1≠origin κ := by
  intro he
  have hz := z.2.1
  rw [he] at hz
  simp [origin,hε] at hz

lemma anisotropic_zero (hχ : quadraticChar F (-1:F)= -1) (x y : F)
    (h : x^2+y^2=0) : x=0 ∧ y=0 := by
  have hy : y=0 := by
    by_contra hy
    have hs : IsSquare (-1:F) := by
      refine ⟨x/y,?_⟩
      field_simp [hy]
      linear_combination -h
    exact (quadraticChar_neg_one_iff_not_isSquare.mp hχ) hs
  have hx : x=0 := by
    rw [hy,zero_pow (by decide : (2:ℕ)≠0),add_zero,pow_two] at h
    exact (mul_eq_zero.mp h).elim id id
  exact ⟨hx,hy⟩

@[expose] def center (κ ε η : F) (hε : ε^2=1) (hη : η^2=1) : Bad κ ε η :=
  ⟨⟨((-ε,0),(-η,0),0),by simp [hε,hη]⟩,by simp⟩

/-- The inert forbidden adjacent-norm locus is one actual vector, not just
an upper-bound estimate: (−epsilon,0,−eta,0,0). -/
theorem inert_unique (κ ε η : F) (hκ : κ≠0) (hε : ε^2=1) (hη : η^2=1)
    (hχ : quadraticChar F (-1:F)= -1) (z : Bad κ ε η) :
    z=center κ ε η hε hη := by
  let a := z.1.1.1.1
  let b := z.1.1.1.2
  let c := z.1.1.2.1.1
  let d := z.1.1.2.1.2
  let w := z.1.1.2.2
  obtain ⟨ha',hb⟩ := anisotropic_zero hχ (a+ε) b z.2.1
  obtain ⟨hc',hd⟩ := anisotropic_zero hχ (c+η) d z.2.2
  have ha : a= -ε := by linear_combination ha'
  have hc : c= -η := by linear_combination hc'
  have he := z.1.2
  change a^2+b^2-(c^2+d^2)=κ*w^2 at he
  rw [ha,hb,hc,hd] at he
  simp only [neg_sq,hε,hη,zero_pow (by decide : (2:ℕ)≠0),add_zero,sub_self] at he
  have hw : w=0 := pow_eq_zero ((mul_eq_zero.mp he.symm).resolve_left hκ)
  apply Subtype.ext
  apply Subtype.ext
  change ((a,b),(c,d),w)=((-ε,0),(-η,0),0)
  rw [ha,hb,hc,hd,hw]

theorem inert_card (κ ε η : F) (hκ : κ≠0) (hε : ε^2=1) (hη : η^2=1)
    (hχ : quadraticChar F (-1:F)= -1) : Nat.card (Bad κ ε η)=1 := by
  classical
  letI : Unique (Bad κ ε η) :=
    { default := center κ ε η hε hη
      uniq := inert_unique κ ε η hκ hε hη hχ }
  simp only [Nat.card_eq_fintype_card,Fintype.card_unique]

lemma affine_relation (κ ε η : F) (hε : ε^2=1) (hη : η^2=1) (z : Bad κ ε η) :
    -2*ε*z.1.1.1.1+2*η*z.1.1.2.1.1=κ*z.1.1.2.2^2 := by
  linear_combination z.1.2-z.2.1+z.2.2+hε-hη

end FiniteAdjacentNormLocus318
