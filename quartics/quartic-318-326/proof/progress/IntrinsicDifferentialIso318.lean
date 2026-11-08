module
public import IntrinsicDifferentialFunctor318
public section
noncomputable section
namespace IntrinsicDifferentialIso318
open AlgebraicGeometry CategoryTheory Opposite
open IntrinsicDifferentialPullback318 IntrinsicDifferentialFunctor318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} {R : CommRingCat.{u}}

lemma inverse_over_base (e : X ≅ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (he : e.hom ≫ q = p) : e.inv ≫ p = q := by
  rw [←he]
  simp

/-- The actual additive pullback equivalence on intrinsic global differentials.
Its inverse is pullback by the specified inverse Scheme morphism. -/
@[expose] def globalEquiv (e : X ≅ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (he : e.hom ≫ q = p) : Γ(FamilyIntrinsicDifferentials318.omega q, ⊤) ≃+
      Γ(FamilyIntrinsicDifferentials318.omega p, ⊤) where
  toFun := globalSection e.hom p q he
  invFun := globalSection e.inv q p (inverse_over_base e p q he)
  left_inv s := by
    have hcomp : (e.inv ≫ e.hom) ≫ q = q := by simp
    calc
      _ = globalSection (e.inv ≫ e.hom) q q hcomp s :=
        (globalSection_comp e.inv e.hom q p q (inverse_over_base e p q he) he hcomp s).symm
      _ = globalSection (𝟙 Y) q q (Category.id_comp q) s :=
        globalSection_congr e.inv_hom_id q q hcomp (Category.id_comp q) s
      _ = s := globalSection_id q _ s
  right_inv s := by
    have hcomp : (e.hom ≫ e.inv) ≫ p = p := by simp
    calc
      _ = globalSection (e.hom ≫ e.inv) p p hcomp s :=
        (globalSection_comp e.hom e.inv p q p he (inverse_over_base e p q he) hcomp s).symm
      _ = globalSection (𝟙 X) p p (Category.id_comp p) s :=
        globalSection_congr e.hom_inv_id p p hcomp (Category.id_comp p) s
      _ = s := globalSection_id p _ s
  map_add' s t := (globalHom e.hom p q he).map_add s t

@[simp] theorem globalEquiv_apply (e : X ≅ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (he : e.hom ≫ q = p) (s : Γ(FamilyIntrinsicDifferentials318.omega q, ⊤)) :
    globalEquiv e p q he s = globalSection e.hom p q he s := rfl

@[simp] theorem globalEquiv_symm_apply (e : X ≅ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (he : e.hom ≫ q = p) (s : Γ(FamilyIntrinsicDifferentials318.omega p, ⊤)) :
    (globalEquiv e p q he).symm s =
      globalSection e.inv q p (inverse_over_base e p q he) s := rfl

theorem identity (p : X ⟶ Spec R) :
    globalEquiv (Iso.refl X) p p (Category.id_comp p) = AddEquiv.refl _ := by
  ext s
  exact globalSection_id p _ s

/-- Exact contravariant composition, not an equivalence selected by a dimension count. -/
theorem composition (e : X ≅ Y) (d : Y ≅ Z)
    (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (r : Z ⟶ Spec R)
    (he : e.hom ≫ q = p) (hd : d.hom ≫ r = q)
    (hed : (e ≪≫ d).hom ≫ r = p) :
    globalEquiv (e ≪≫ d) p r hed =
      (globalEquiv d q r hd).trans (globalEquiv e p q he) := by
  ext s
  exact globalSection_comp e.hom d.hom p q r he hd hed s
end IntrinsicDifferentialIso318
