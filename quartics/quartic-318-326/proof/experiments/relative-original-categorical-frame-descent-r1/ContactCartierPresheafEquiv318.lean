module
public import ContactCartierPointPresheaf318
public section
noncomputable section
namespace ContactCartierPresheafEquiv318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ) (N : ℕ)
/-- The complete two-sided full-ideal classifier assembled as an actual
natural isomorphism, not an equivalence only of field-valued points. -/
@[expose] def equivalence : ContactCartierDataPresheaf318.presheaf c N ≅
    ContactCartierPointPresheaf318.presheaf c N :=
  NatIso.ofComponents (fun T => Equiv.toIso (ContactBoundedCartierEquiv318.equivalence c N T.unop.hom))
    (by
      intro T U f
      funext D
      exact ContactBoundedCartierNaturality318.natural c N _ _ f.unop.left f.unop.w D)
end ContactCartierPresheafEquiv318
