module
public import IntrinsicDifferentialPullback318
public section
noncomputable section
namespace IntrinsicDifferentialFunctor318
open AlgebraicGeometry CategoryTheory Opposite
open IntrinsicDifferentialPullback318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y Z : Scheme.{u}} {R : CommRingCat.{u}}

/-- Canonical differential maps compose through the actual pushforward
composition isomorphism. This is an equality of full sheaf morphisms. -/
theorem map_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (r : Z ⟶ Spec R)
    (hf : f ≫ q = p) (hg : g ≫ r = q)
    (hfg : (f ≫ g) ≫ r = p) :
    map (f ≫ g) p r hfg = map g q r hg ≫
      (Scheme.Modules.pushforward g).map (map f p q hf) ≫
      (Scheme.Modules.pushforwardComp f g).hom.app (FamilyIntrinsicDifferentials318.omega p) := by
  apply UniversalSheafDifferentials318.hom_ext (FamilyIntrinsicDifferentials318.coefficients r)
  ext U a
  change (map (f ≫ g) p r hfg).val.app U ((FamilyIntrinsicDifferentials318.D r).d a) =
    (map f p q hf).val.app (op (g ⁻¹ᵁ U.unop))
      ((map g q r hg).val.app U ((FamilyIntrinsicDifferentials318.D r).d a))
  rw [map_D, map_D, map_D]
  rfl

/-- The canonical identity comparison has the actual identity underlying maps. -/
theorem map_id (p : X ⟶ Spec R) (h : (𝟙 X) ≫ p = p) :
    map (𝟙 X) p p h = (Scheme.Modules.pushforwardId X).inv.app
      (FamilyIntrinsicDifferentials318.omega p) := by
  apply UniversalSheafDifferentials318.hom_ext (FamilyIntrinsicDifferentials318.coefficients p)
  ext U a
  change (map (𝟙 X) p p h).val.app U ((FamilyIntrinsicDifferentials318.D p).d a) =
    (FamilyIntrinsicDifferentials318.D p).d a
  rw [map_D]
  rfl

/-- Pullback on the existing actual global sections is contravariantly functorial. -/
theorem globalSection_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (r : Z ⟶ Spec R)
    (hf : f ≫ q = p) (hg : g ≫ r = q) (hfg : (f ≫ g) ≫ r = p)
    (s : Γ(FamilyIntrinsicDifferentials318.omega r, ⊤)) :
    globalSection (f ≫ g) p r hfg s =
      globalSection f p q hf (globalSection g q r hg s) := by
  exact congrArg (fun k => k.val.app (op ⊤) s) (map_comp f g p q r hf hg hfg)

theorem globalSection_id (p : X ⟶ Spec R) (h : (𝟙 X) ≫ p = p)
    (s : Γ(FamilyIntrinsicDifferentials318.omega p, ⊤)) :
    globalSection (𝟙 X) p p h s = s := by
  exact congrArg (fun k => k.val.app (op ⊤) s) (map_id p h)

/-- Equal actual Scheme maps, regardless of the chosen proof of their base
square, give equal pullbacks of every actual global differential. -/
theorem globalSection_congr {f g : X ⟶ Y} (hfg : f = g)
    (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (hf : f ≫ q = p) (hg : g ≫ q = p)
    (s : Γ(FamilyIntrinsicDifferentials318.omega q, ⊤)) :
    globalSection f p q hf s = globalSection g p q hg s := by
  subst g
  rfl

@[expose] def globalHom (f : X ⟶ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (h : f ≫ q = p) : Γ(FamilyIntrinsicDifferentials318.omega q, ⊤) →+
      Γ(FamilyIntrinsicDifferentials318.omega p, ⊤) :=
  ((map f p q h).val.app (op ⊤)).hom.toAddMonoidHom

@[simp] theorem globalHom_apply (f : X ⟶ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (h : f ≫ q = p) (s : Γ(FamilyIntrinsicDifferentials318.omega q, ⊤)) :
    globalHom f p q h s = globalSection f p q h s := rfl

theorem globalSection_neg (f : X ⟶ Y) (p : X ⟶ Spec R) (q : Y ⟶ Spec R)
    (h : f ≫ q = p) (s : Γ(FamilyIntrinsicDifferentials318.omega q, ⊤)) :
    globalSection f p q h (-s) = -globalSection f p q h s :=
  (globalHom f p q h).map_neg s
end IntrinsicDifferentialFunctor318
