module
public import FourRootActualSheafLengths318
public section
noncomputable section
namespace PrincipalQuotientComplexPoint318
open AlgebraicGeometry CategoryTheory
variable {R : Type} [CommRing R]
/-- At the SAME evaluated scheme point, membership in the actual
principal quotient image is precisely vanishing of the original
coefficient. The reverse direction constructs the quotient evaluation. -/
theorem image_iff (a : R) (f : R →+* ℂ) :
    (Spec.map (CommRingCat.ofHom f)) default ∈
      Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) ↔
        f a = 0 := by
  constructor
  · rintro ⟨q,hq⟩
    have ha : a ∈ ((Spec.map (CommRingCat.ofHom f)) default).asIdeal := by
      rw [←hq]
      change Ideal.Quotient.mk (Ideal.span {a}) a ∈ q.asIdeal
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton a))]
      exact Ideal.zero_mem _
    rw [FourRootActualSheafLengths318.complex_point] at ha
    exact ha
  · intro ha
    have hk : Ideal.span {a} ≤ RingHom.ker f := by
      apply Ideal.span_le.mpr
      intro x hx
      rw [Set.mem_singleton_iff.mp hx]
      exact ha
    let g : (R ⧸ Ideal.span {a}) →+* ℂ := Ideal.Quotient.lift _ f (fun x hx => hk hx)
    refine ⟨(Spec.map (CommRingCat.ofHom g)) default,?_⟩
    change (Spec.map (CommRingCat.ofHom g) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})))) default = _
    rw [←Spec.map_comp]
    have he : CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {a})) ≫
        CommRingCat.ofHom g = CommRingCat.ofHom f := by
      ext x
      rfl
    rw [he]
end PrincipalQuotientComplexPoint318
