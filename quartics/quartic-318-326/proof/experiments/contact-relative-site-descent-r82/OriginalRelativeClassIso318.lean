module
public import OriginalOpenFamilyTest318
public section
noncomputable section
namespace OriginalRelativeClassIso318
open AlgebraicGeometry CategoryTheory RelativeLineClassQuotient318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y S : Scheme.{u}} (p : X ⟶ S) (q : Y ⟶ S) (i : Y ≅ X)
  (h : i.hom ≫ p = q ≫ 𝟙 S)

include h in
lemma inverse_square : i.inv ≫ q = p ≫ 𝟙 S := by
  have hh : i.hom ≫ p = q := by simpa only [Category.comp_id] using h
  rw [← hh,Iso.inv_hom_id_assoc,Category.comp_id]

/-- An actual family isomorphism acts by the original relative pullback
homomorphisms in both directions, rather than a new quotient equivalence. -/
@[expose] def equivalence : RelativeClass p ≃* RelativeClass q where
  toFun := RelativeLineClassQuotient318.map p q i.hom (𝟙 S) h
  invFun := RelativeLineClassQuotient318.map q p i.inv (𝟙 S) (inverse_square p q i h)
  map_mul' := (RelativeLineClassQuotient318.map p q i.hom (𝟙 S) h).map_mul
  left_inv c := by
    have hc := RelativeLineClassQuotient318.map_composition p q p i.hom (𝟙 S) i.inv (𝟙 S)
      h (inverse_square p q i h) (by simp only [i.inv_hom_id,Category.id_comp,Category.comp_id])
    have hh := congrArg (fun k => k c) hc
    simpa only [i.inv_hom_id,Category.id_comp,RelativeLineClassQuotient318.map_identity,
      MonoidHom.id_apply,MonoidHom.comp_apply] using hh.symm
  right_inv c := by
    have hc := RelativeLineClassQuotient318.map_composition q p q i.inv (𝟙 S) i.hom (𝟙 S)
      (inverse_square p q i h) h (by simp only [i.hom_inv_id,Category.id_comp,Category.comp_id])
    have hh := congrArg (fun k => k c) hc
    simpa only [i.hom_inv_id,Category.id_comp,RelativeLineClassQuotient318.map_identity,
      MonoidHom.id_apply,MonoidHom.comp_apply] using hh.symm
end OriginalRelativeClassIso318
