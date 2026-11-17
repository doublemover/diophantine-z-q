module
public import Mathlib.Tactic
public section
namespace AdditiveTorsionTransfer318

/-- A genuine additive equivalence transports every finite-exponent torsion
kernel. No finiteness, divisibility or rank hypothesis is inserted. -/
def torsionEquiv {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (m : ℕ) :
    (nsmulAddMonoidHom (α:=G) m).ker ≃+
      (nsmulAddMonoidHom (α:=H) m).ker where
  toFun x := ⟨e x.val, by
    change m • e x.val=0
    rw [←map_nsmul]
    have hx : m • x.val=0 := x.property
    rw [hx,map_zero]⟩
  invFun y := ⟨e.symm y.val, by
    change m • e.symm y.val=0
    rw [←map_nsmul]
    have hy : m • y.val=0 := y.property
    rw [hy,map_zero]⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val
  map_add' x y := by apply Subtype.ext; exact e.map_add x.val y.val

lemma torsion_card_eq {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (e : G ≃+ H) (m : ℕ) :
    Nat.card (nsmulAddMonoidHom (α:=G) m).ker =
      Nat.card (nsmulAddMonoidHom (α:=H) m).ker :=
  Nat.card_congr (torsionEquiv e m).toEquiv

end AdditiveTorsionTransfer318
