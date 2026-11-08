module
public import AlgebraChartEdges318
public section
noncomputable section
namespace AlgebraChartCompatibility318
open AlgebraicGeometry CategoryTheory
open AlgebraChartEvaluation318 AlgebraChartEdges318
set_option maxHeartbeats 800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]
@[expose] def Input (A B:R) := (F A B →ₐ[R] S) ⊕ (I A B →ₐ[R] S)
@[expose] def image (A B:R) : Input (S:=S) A B → (Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B)
  | .inl f => finiteInput A B f
  | .inr f => infinityInput A B f
@[expose] def evaluate (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2))) :
    Input (S:=S) A B → Input (S:=S) A B → (Spec (CommRingCat.of S) ⟶ WeierstrassGluing318.scheme A B)
  | .inl f,.inl g => finite A B hD f g
  | .inl f,.inr g => mixed A B hD g f
  | .inr f,.inl g => mixed A B hD f g
  | .inr f,.inr g => both A B hD f g

theorem evaluate_congr_left (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (p p' q:Input (S:=S) A B) (h:image A B p=image A B p') :
    evaluate A B hD p q=evaluate A B hD p' q := by
  cases p with
  | inl f =>
    cases p' with
    | inl g =>
      have he:=ChartInputEquality318.finite_injective A B f g h
      subst g
      rfl
    | inr g =>
      cases q with
      | inl k => exact (mixed_to_finite A B hD g k f h.symm).symm
      | inr k => exact (both_left_to_mixed A B hD g k f h.symm).symm
  | inr f =>
    cases p' with
    | inl g =>
      cases q with
      | inl k => exact mixed_to_finite A B hD f k g h
      | inr k => exact both_left_to_mixed A B hD f k g h
    | inr g =>
      have he:=ChartInputEquality318.infinity_injective A B f g h
      subst g
      rfl

theorem evaluate_congr_right (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (p q q':Input (S:=S) A B) (h:image A B q=image A B q') :
    evaluate A B hD p q=evaluate A B hD p q' := by
  cases q with
  | inl f =>
    cases q' with
    | inl g =>
      have he:=ChartInputEquality318.finite_injective A B f g h
      subst g
      rfl
    | inr g =>
      cases p with
      | inl k => exact (finite_comm A B hD k f).trans (mixed_to_finite A B hD g k f h.symm).symm
      | inr k => exact (both_right_to_mixed A B hD k g f h.symm).symm
  | inr f =>
    cases q' with
    | inl g =>
      cases p with
      | inl k => exact (mixed_to_finite A B hD f k g h).trans (finite_comm A B hD g k)
      | inr k => exact both_right_to_mixed A B hD k f g h
    | inr g =>
      have he:=ChartInputEquality318.infinity_injective A B f g h
      subst g
      rfl

/-- The four actual local laws agree whenever both actual completed-curve inputs
agree, for every commutative coefficient algebra, including nonreduced algebras. -/
theorem evaluate_congr (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
    (p p' q q':Input (S:=S) A B) (hp:image A B p=image A B p') (hq:image A B q=image A B q') :
    evaluate A B hD p q=evaluate A B hD p' q' :=
  (evaluate_congr_left A B hD p p' q hp).trans (evaluate_congr_right A B hD p' q q' hq)
end AlgebraChartCompatibility318
