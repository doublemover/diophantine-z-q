module
public import ModuleLocalGluing318
public section
noncomputable section
namespace ModuleLocalInverse318
open AlgebraicGeometry CategoryTheory Opposite ModuleLocalGluing318
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
  {ι : Type u} (U : ι → X.Opens) (hc : ⊤ ≤ iSup U)
  (hb : ∀ i V, V≤U i → Function.Bijective (f.app V))

lemma natural (V W : X.Opens) (h : W≤V) (a : Γ(M,V)) :
    res N h (f.app V a)=f.app W (res M h a) := by
  exact (congrArg (fun k => k a) (f.val.naturality (homOfLE h).op)).symm

/-- Actual inverses on every subopen, with the original forward map fixed. -/
@[expose] def localInverse (i : ι) (V : X.Opens) (h : V≤U i) :
    Γ(N,V) →ₗ[Γ(X,V)] Γ(M,V) :=
  (LinearEquiv.ofBijective (f.val.app (op V)).hom (hb i V h)).symm.toLinearMap

lemma forward_inverse (i : ι) (V : X.Opens) (h : V≤U i) (a : Γ(N,V)) :
    f.app V (localInverse f U hb i V h a)=a :=
  (LinearEquiv.ofBijective (f.val.app (op V)).hom (hb i V h)).apply_symm_apply a
lemma inverse_forward (i : ι) (V : X.Opens) (h : V≤U i) (a : Γ(M,V)) :
    localInverse f U hb i V h (f.app V a)=a :=
  (LinearEquiv.ofBijective (f.val.app (op V)).hom (hb i V h)).symm_apply_apply a

@[expose] def inverseData : LocalData N M U where
  map := localInverse f U hb
  natural i V W hV hW a := by
    apply (hb i W (hW.trans hV)).1
    rw [← natural f,forward_inverse,forward_inverse]
  compatible i j V hi hj a := by
    apply (hb i V hi).1
    rw [forward_inverse,forward_inverse]

/-- Global inverse is glued from the exact original local inverse maps,
not obtained from bijectivity of underlying scheme points. -/
@[expose] def inverse : N ⟶ M := ModuleLocalGluing318.hom (inverseData f U hb) hc

lemma inverse_on_subopen (i : ι) (V : X.Opens) (h : V≤U i) (a : Γ(N,V)) :
    (inverse f U hc hb).app V a=localInverse f U hb i V h a := by
  have he := value_subopen (inverseData f U hb) hc V V le_rfl i h a
  simpa only [res_self] using he

lemma inverse_hom : inverse f U hc hb ≫ f=𝟙 N := by
  apply Scheme.Modules.hom_ext
  intro V
  ext a
  apply ext_value hc V
  intro i
  change res N (show V⊓U i≤V from inf_le_left)
    (f.app V ((inverse f U hc hb).app V a))=res N inf_le_left a
  rw [natural f,natural (inverse f U hc hb),inverse_on_subopen f U hc hb i _ inf_le_right,
    forward_inverse]

lemma hom_inverse : f ≫ inverse f U hc hb=𝟙 M := by
  apply Scheme.Modules.hom_ext
  intro V
  ext a
  apply ext_value hc V
  intro i
  change res M (show V⊓U i≤V from inf_le_left)
    ((inverse f U hc hb).app V (f.app V a))=res M inf_le_left a
  rw [natural (inverse f U hc hb),natural f,
    inverse_on_subopen f U hc hb i _ inf_le_right,inverse_forward]

/-- Full-cover descent for module isomorphisms, retaining the supplied
forward morphism exactly and checking both composites on every subopen. -/
@[expose] def iso : M ≅ N where
  hom := f
  inv := inverse f U hc hb
  hom_inv_id := hom_inverse f U hc hb
  inv_hom_id := inverse_hom f U hc hb
end ModuleLocalInverse318
