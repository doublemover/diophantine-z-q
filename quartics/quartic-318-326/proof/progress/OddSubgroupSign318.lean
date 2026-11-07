module
public import GlobalIndexHeight318
public section
namespace OddSubgroupSign318
variable {G:Type*} [AddCommGroup G]

lemma odd_zsmul_two_torsion (T:G) (hT:T+T=0) (n:ℤ) (hn:Odd n) : n • T=T := by
  obtain ⟨k,hk⟩:=hn
  rw [hk,add_zsmul,one_zsmul]
  have hh:(2*k) • T=0 := by
    rw [mul_comm,mul_zsmul,two_zsmul,hT,zsmul_zero]
  rw [hh,zero_add]

/-- An odd multiple lying in a subgroup excludes every translated multiple
by a nonzero2-torsion class. No finiteness or compactness premise is needed. -/
theorem odd_multiple_excludes_translate (S:AddSubgroup G) (P T:G)
    (hT:T+T=0) (hTS:T∉S) (n:ℤ) (hn:Odd n) (hnS:n • P∈S) (m:ℤ) :
    m • P+T∉S := by
  intro hmS
  have h1:=S.zsmul_mem hmS n
  have h2:=S.zsmul_mem hnS m
  have he:n • (m • P+T)-m • (n • P)=T := by
    rw [zsmul_add,smul_comm n m P,odd_zsmul_two_torsion T hT n hn]
    abel
  apply hTS
  rw [←he]
  exact S.sub_mem h1 h2

/-- The exact weak-sign alternative required for product-height additivity.
`negative` is subgroup membership and `positive` is translated membership. -/
theorem common_weak_sign {ι:Type*} (S:AddSubgroup G) (P T:G)
    (hT:T+T=0) (hTS:T∉S) (n:ι→ℤ) (hn:∀i,Odd (n i)) :
    (∀i,n i • P∉S) ∨ (∀i,n i • P+T∉S) := by
  classical
  by_cases h:∀i,n i • P∉S
  · exact Or.inl h
  · push_neg at h
    obtain ⟨i,hi⟩:=h
    exact Or.inr (fun j=>odd_multiple_excludes_translate S P T hT hTS (n i) (hn i) hi (n j))

#print axioms odd_multiple_excludes_translate
#print axioms common_weak_sign
end OddSubgroupSign318
