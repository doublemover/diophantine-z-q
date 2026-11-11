module
public import RegularClosedKernelTransport318
public section
noncomputable section
namespace ContactBoundedCartierEquiv318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B : Scheme.{0}} (b : B ⟶ Spec (CommRingCat.of ℚ))
/-- Intrinsic bounded standard quotients WITH actual regular local
quotient charts on the original source. This extra condition is explicit. -/
abbrev Data := {D : ContactBoundedSchemeHilbertData318.Data c N b //
  OriginalRegularClosedCharts318.Property D.ideal.subschemeι}
/-- The corresponding subset of actual bounded parameter points is
specified on the actual entire universal fiber, not by chart choices. -/
abbrev Point := {f : ContactBoundedPointFamily318.SchemePoint c N b //
  OriginalRegularClosedCharts318.Property (ContactBoundedPointFamily318.into c N b f)}
@[expose] def forward (D : Data c N b) : Point c N b :=
  ⟨ContactBoundedHilbertEquiv318.equivalence c N b D.val,
    RegularClosedIso318.transport D.val.ideal.subschemeι _
      (ContactBoundedInputRecovery318.comparison c N b D.val)
      (ContactBoundedInputRecovery318.comparison_source c N b D.val) D.property⟩
@[expose] def backward (f : Point c N b) : Data c N b :=
  ⟨ContactBoundedPointFamily318.extract c N b f.val,
    RegularClosedIso318.transport (ContactBoundedPointFamily318.into c N b f.val) _
      (ClosedFamilyCanonicalProperties318.comparison (ContactBoundedPointFamily318.into c N b f.val))
      (ClosedFamilyCanonicalProperties318.comparison_source (ContactBoundedPointFamily318.into c N b f.val)) f.property⟩
/-- The proved Hilbert equivalence restricts EXACTLY to genuine original
Cartier input and genuine Cartier universal fibers on all scheme bases.
No claim that this subset is all points or a represented open is made. -/
@[expose] def equivalence : Data c N b ≃ Point c N b where
  toFun := forward c N b
  invFun := backward c N b
  left_inv D := by apply Subtype.ext; exact (ContactBoundedHilbertEquiv318.equivalence c N b).symm_apply_apply D.val
  right_inv f := by apply Subtype.ext; exact (ContactBoundedHilbertEquiv318.equivalence c N b).apply_symm_apply f.val
end ContactBoundedCartierEquiv318
