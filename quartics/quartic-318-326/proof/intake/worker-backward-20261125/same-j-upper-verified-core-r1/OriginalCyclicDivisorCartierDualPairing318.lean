module
public import OriginalCyclicDivisorCartierAllOpenFrames318

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorCartierDualPairing318

open AlgebraicGeometry CategoryTheory TopCat TopologicalSpace Opposite
open OriginalCyclicDivisorCartierAllOpenFrames318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Z X : Scheme.{u}} (p : Z ⟶ X)

/-- A local dual section is an actual O-linear map from the original
ideal to the structure sheaf, on *every* smaller open, with the true
restriction identity. Its domain is not a replacement cocycle module. -/
structure Dual (W : X.Opens) where
  app (U : X.Opens) (h : U ≤ W) : I (p:=p) U →ₗ[Γ(X,U)] Γ(X,U)
  natural {U V : X.Opens} (h : V ≤ W) (l : U ≤ V) (a : I (p:=p) V) :
    ρ l (app V h a)=app U (l.trans h) (ires (p:=p) l a)

variable {p}

theorem dual_ext {W : X.Opens} {e f : Dual p W}
    (h : ∀ U k (a : I (p:=p) U), e.app U k a=f.app U k a) : e=f := by
  cases e with
  | mk ea en =>
    cases f with
    | mk fa fn =>
      have he : ea=fa := by
        funext U k
        apply LinearMap.ext
        exact h U k
      cases he
      rfl

def restrict {U W : X.Opens} (l : U ≤ W) (b : Dual p W) : Dual p U where
  app V h := b.app V (h.trans l)
  natural h k a := b.natural (h.trans l) k a

/-- No chosen frame: the canonical section of the positive Cartier
dual is the inclusion of the actual kernel in O_X. -/
def canonical (W : X.Opens) : Dual p W where
  app U _ := (I (p:=p) U).subtype
  natural _ _ _ := rfl

theorem canonical_restrict {U W : X.Opens} (l : U ≤ W) :
    restrict l (canonical (p:=p) W)=canonical (p:=p) U := rfl

theorem ρ_self {W : X.Opens} (b : Γ(X,W)) : ρ (le_rfl : W ≤ W) b=b := by
  let j : W ⟶ W := homOfLE le_rfl
  change X.presheaf.map j.op b=b
  have hj : j.op = 𝟙 (op W) := Subsingleton.elim _ _
  have hm : X.presheaf.map j.op = 𝟙 (X.presheaf.obj (op W)) :=
    (congrArg X.presheaf.map hj).trans (X.presheaf.map_id (op W))
  exact congrArg (fun f : Γ(X,W) ⟶ Γ(X,W) => f b) hm

variable [IsClosedImmersion p]
variable (Q : Chart p) {W : X.Opens} (h : W ≤ Q.V.1)

def generator : I (p:=p) W := ⟨coeff Q h,coeff_mem Q h⟩

theorem frame_one : frame Q h 1=generator Q h := by
  apply Subtype.ext
  change 1*coeff Q h=coeff Q h
  exact one_mul _

theorem generator_restrict {U : X.Opens} (l : U ≤ W) :
    ires (p:=p) l (generator Q h)=generator Q (l.trans h) :=
  Subtype.ext (coeff_restrict Q h l)

theorem coord_mul (a : I (p:=p) W) :
    (frame Q h).symm a * coeff Q h=a.val :=
  congrArg Subtype.val ((frame Q h).apply_symm_apply a)

/-- Actual dual function with a prescribed coefficient in the
reciprocal frame: evaluate the unique O-coordinate of an ideal section. -/
def ofCoeff (b : Γ(X,W)) : Dual p W where
  app U l :=
    { toFun := fun a=>ρ l b * (frame Q (l.trans h)).symm a
      map_add' := by
        intro a a'
        change ρ l b * (frame Q (l.trans h)).symm (a+a') =
          ρ l b * (frame Q (l.trans h)).symm a + ρ l b * (frame Q (l.trans h)).symm a'
        rw [map_add,mul_add]
      map_smul' := by
        intro r a
        change ρ l b * (frame Q (l.trans h)).symm (r • a) =
          r * (ρ l b * (frame Q (l.trans h)).symm a)
        rw [map_smul,smul_eq_mul]
        exact mul_left_comm _ _ _ }
  natural l k a := by
    change ρ k (ρ l b * (frame Q (l.trans h)).symm a) =
      ρ (k.trans l) b * (frame Q (k.trans (l.trans h))).symm (ires (p:=p) k a)
    rw [map_mul,ρ_comp,coord_restrict Q (l.trans h) k]

def read (b : Dual p W) : Γ(X,W) := b.app W le_rfl (generator Q h)

theorem read_ofCoeff (b : Γ(X,W)) : read Q h (ofCoeff Q h b)=b := by
  change ρ (le_rfl : W ≤ W) b * (frame Q h).symm (generator Q h)=b
  rw [←frame_one,LinearEquiv.symm_apply_apply,mul_one,ρ_self]

theorem ofCoeff_read (b : Dual p W) : ofCoeff Q h (read Q h b)=b := by
  apply dual_ext
  intro U l a
  let d := (frame Q (l.trans h)).symm a
  have he : d • generator Q (l.trans h)=a := by
    apply Subtype.ext
    exact coord_mul Q (l.trans h) a
  have eq := (b.natural (le_rfl : W ≤ W) l (generator Q h)).trans
    (congrArg (b.app U l) (generator_restrict Q h l))
  change ρ l (b.app W le_rfl (generator Q h))*d=b.app U l a
  calc
    _ = d*(b.app U l (generator Q (l.trans h))) :=
      (mul_comm _ d).trans (congrArg (fun x=>d*x) eq)
    _ = b.app U l (d • generator Q (l.trans h)) :=
      ((b.app U l).map_smul d (generator Q (l.trans h))).symm
    _ = _ := congrArg (b.app U l) he

/-- Local duality on the whole chart including its non-affine opens.
Evaluation of the two literal bases is 1, by the displayed inverse. -/
def coordinate : Dual p W ≃ Γ(X,W) where
  toFun := read Q h
  invFun := ofCoeff Q h
  left_inv := ofCoeff_read Q h
  right_inv := read_ofCoeff Q h

theorem read_canonical : read Q h (canonical (p:=p) W)=coeff Q h := rfl

/-- The canonical dual section cuts precisely the full original
ideal on the genuine affine open, including nilpotent multiplicity. -/
theorem canonical_ideal (V : X.affineOpens) (hV : V≤Q.V) :
    Ideal.span {read Q hV (canonical (p:=p) V.1)}=p.ker.ideal V := by
  change Ideal.span (Set.singleton (OriginalCyclicDivisorCartierAffineFrames318.equation
    Q.A Q.j Q.c V hV) : Set Γ(X,V.1)) = p.ker.ideal V
  exact (OriginalCyclicDivisorCartierAffineFrames318.ideal_eq
    p Q.A Q.j Q.c Q.z Q.square V hV).symm

section Transitions

variable (P : Chart p) (k : W ≤ P.V.1)

abbrev numerator := (frame P k).symm (generator Q h)
abbrev denominator := (frame Q h).symm (generator P k)

theorem numerator_read : numerator Q h P k * coeff P k=coeff Q h :=
  coord_mul P k (generator Q h)

theorem denominator_read : denominator Q h P k * coeff Q h=coeff P k :=
  coord_mul Q h (generator P k)

theorem transition_inverse : numerator Q h P k * denominator Q h P k=1 := by
  apply cancel_coeff P k
  calc
    _ = denominator Q h P k * (numerator Q h P k * coeff P k) := by
      rw [mul_comm (numerator Q h P k) (denominator Q h P k),mul_assoc]
    _ = denominator Q h P k * coeff Q h := by rw [numerator_read]
    _ = coeff P k := denominator_read Q h P k
    _ = _ := (one_mul _).symm

/-- Positive dual transition: the coordinate on Q is this unit times
the coordinate on P. It comes from dividing two bases of one ideal. -/
def transition : Γ(X,W)ˣ :=
  ⟨numerator Q h P k,denominator Q h P k,transition_inverse Q h P k,
    (mul_comm _ _).trans (transition_inverse Q h P k)⟩

theorem transition_read : (transition Q h P k : Γ(X,W))*coeff P k=coeff Q h :=
  numerator_read Q h P k

theorem transition_unique (v : Γ(X,W)ˣ) (hv : (v:Γ(X,W))*coeff P k=coeff Q h) :
    v=transition Q h P k := by
  apply Units.ext
  apply cancel_coeff P k
  exact hv.trans (transition_read Q h P k).symm

theorem transition_restrict {U : X.Opens} (l : U≤W) :
    Units.map (ρ l).toMonoidHom (transition Q h P k)=transition Q (l.trans h) P (l.trans k) := by
  apply transition_unique Q (l.trans h) P (l.trans k)
  change ρ l (transition Q h P k : Γ(X,W))*coeff P (l.trans k)=coeff Q (l.trans h)
  rw [←coeff_restrict P k l,←map_mul,transition_read Q h P k,coeff_restrict Q h l]

theorem transition_cocycle (R : Chart p) (t : W≤R.V.1) :
    transition Q h P k * transition P k R t=transition Q h R t := by
  apply transition_unique Q h R t
  rw [Units.val_mul,mul_assoc,transition_read P k R t,transition_read Q h P k]

theorem read_transition (b : Dual p W) :
    read Q h b=(transition Q h P k : Γ(X,W))*read P k b := by
  have he : (transition Q h P k : Γ(X,W)) • generator P k=generator Q h :=
    Subtype.ext (transition_read Q h P k)
  change b.app W le_rfl (generator Q h) =
    (transition Q h P k : Γ(X,W))*b.app W le_rfl (generator P k)
  exact (congrArg (b.app W le_rfl) he.symm).trans
    ((b.app W le_rfl).map_smul _ _)

end Transitions
end OriginalCyclicDivisorCartierDualPairing318

#print axioms OriginalCyclicDivisorCartierDualPairing318.coordinate
#print axioms OriginalCyclicDivisorCartierDualPairing318.canonical_ideal
#print axioms OriginalCyclicDivisorCartierDualPairing318.transition_cocycle
