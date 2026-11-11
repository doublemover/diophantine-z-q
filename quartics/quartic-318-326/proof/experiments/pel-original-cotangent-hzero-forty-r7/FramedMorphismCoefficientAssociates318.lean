module
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Ring
public section
noncomputable section
namespace FramedMorphismCoefficientAssociates318
variable {R M N:Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N]
  (e:R≃ₗ[R]M)(f:R≃ₗ[R]N)(d:M→ₗ[R]N)
/-- Exact regular-frame coefficient relation derived from the actual
map on actual generators, before any ideal comparison. -/
theorem coefficient_relation(s:M)(t:N)(a:R)(h:d s=a • t):
    e.symm s*f.symm (d (e 1))=a*f.symm t:=by
  have hs:s=(e.symm s) • e 1:=by
    rw [←e.map_smul,smul_eq_mul,mul_one,e.apply_symm_apply]
  have he:=congrArg f.symm h
  rw [hs] at he
  simpa only [map_smul,smul_eq_mul] using he
/-- Actual generator units give an explicitly produced unit relating
the extracted arrow coefficient to the literal coefficient. Nothing
is inferred from equal support, generic order or desired divisor. -/
theorem unit_multiple(s:M)(t:N)(a:R)(h:d s=a • t)
    (hs:IsUnit (e.symm s))(ht:IsUnit (f.symm t)):
    ∃u:Rˣ,f.symm (d (e 1))=u.val*a:=by
  obtain ⟨v,hv⟩:=hs
  obtain ⟨w,hw⟩:=ht
  refine ⟨v⁻¹*w,?_⟩
  have hr:=coefficient_relation e f d s t a h
  rw [←hv,←hw] at hr
  have hh:=congrArg (fun z:R=>(v⁻¹).val*z) hr
  have he:f.symm (d (e 1))=(v⁻¹).val*(a*w.val):=by
    simpa only [←mul_assoc,Units.inv_mul,one_mul] using hh
  change f.symm (d (e 1))=((v⁻¹).val*w.val)*a
  rw [he]
  ring
/-- Exact principal ideals, including their multiplicities, are equal.
No radical is taken. -/
theorem span_eq(s:M)(t:N)(a:R)(h:d s=a • t)
    (hs:IsUnit (e.symm s))(ht:IsUnit (f.symm t)):
    Ideal.span {f.symm (d (e 1))}=Ideal.span {a}:=by
  obtain ⟨u,hu⟩:=unit_multiple e f d s t a h hs ht
  rw [hu]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton a))
  · apply Ideal.span_le.mpr
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    change a ∈ Ideal.span {u.val*a}
    have hm:=Ideal.mul_mem_left (Ideal.span {u.val*a}) (u⁻¹).val
      (Ideal.subset_span (Set.mem_singleton (u.val*a)))
    simpa only [←mul_assoc,Units.inv_mul,one_mul] using hm
end FramedMorphismCoefficientAssociates318
