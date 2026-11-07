module
public import FirstPrimeParity318
public section
namespace FirstFieldClasses318
open ConcreteG8Domain EuclideanSqrtTwo318 FractionSqrtTwo318 SquareFactorization318 FirstPrimeParity318
set_option maxHeartbeats 0
noncomputable section

theorem field_square_unit (x:K) (hx:x≠0) (hv:EvenAtAllPrimes x) :
    ∃(z:K)(u:Oˣ),z≠0 ∧ x=z^2*toK (u:O) := by
  obtain ⟨a,b,ha,hb,hea,heb,hf⟩:=reduced_even_multiplicity x hx hv
  obtain ⟨r,u,hu⟩:=integral_square_unit a ha hea
  obtain ⟨t,v,hv⟩:=integral_square_unit b hb heb
  let w:Oˣ:=u*v⁻¹
  let z:K:=toK r/toK t
  have ht:t≠0 := by intro hh; rw [hh,zero_pow (by decide),zero_mul] at hv; exact hb hv.symm
  have htk:toK t≠0:=fun hh=>ht (toK_injective (by simpa using hh))
  have hvk:toK (v:O)≠0:=(v.isUnit.map toK).ne_zero
  have hwi:toK (↑(v⁻¹):O)=(toK (v:O))⁻¹ := by
    rw [inv_eq_one_div (toK (v:O))]
    apply (eq_div_iff hvk).mpr
    rw [←map_mul,Units.inv_mul,map_one]
  have hw:toK (w:O)=toK (u:O)/(toK (v:O)) := by
    simp only [w,Units.val_mul,map_mul,hwi,div_eq_mul_inv]
  have he:z^2*toK (w:O)=x := by
    rw [hf,←hu,←hv]
    simp only [map_mul,map_pow]
    rw [hw]
    dsimp only [z]
    field_simp
  have hz:z≠0 := by intro hh; rw [hh,zero_pow (by decide),zero_mul] at he; exact hx he.symm
  exact ⟨z,w,hz,he.symm⟩

/-- Every fraction with even prime values lies in one of the four unit
squareclasses, using the actual unit computation. -/
theorem field_four_classes (x:K) (hx:x≠0) (hv:EvenAtAllPrimes x) :
    ∃r:K,r≠0 ∧ (x=r^2 ∨ x= -r^2 ∨
      x=pair 1 1*r^2 ∨ x= -(pair 1 1)*r^2) := by
  obtain ⟨z,u,hz,he⟩:=field_square_unit x hx hv
  obtain ⟨k,hk,hu|hu|hu|hu⟩:=UnitSquareclasses318.unit_four_classes u
  · refine ⟨z*k,mul_ne_zero hz hk,Or.inl ?_⟩; rw [he,hu]; ring
  · refine ⟨z*k,mul_ne_zero hz hk,Or.inr (Or.inl ?_)⟩; rw [he,hu]; ring
  · refine ⟨z*k,mul_ne_zero hz hk,Or.inr (Or.inr (Or.inl ?_))⟩; rw [he,hu]; ring
  · refine ⟨z*k,mul_ne_zero hz hk,Or.inr (Or.inr (Or.inr ?_))⟩; rw [he,hu]; ring

end
end FirstFieldClasses318
#print axioms FirstFieldClasses318.field_four_classes
