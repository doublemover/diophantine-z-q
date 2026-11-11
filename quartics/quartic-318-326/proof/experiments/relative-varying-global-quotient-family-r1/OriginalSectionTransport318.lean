module
public import OriginalUnitOpenFunctoriality318
public section
noncomputable section
namespace OriginalSectionTransport318
open AlgebraicGeometry CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X Y Z : Scheme.{0}}
@[expose] def move (M : X.Modules) {U V : X.Opens} (h : U = V) : Γ(M,U) →+ Γ(M,V) :=
  (M.presheaf.map (eqToHom h.symm).op).hom
lemma move_refl (M : X.Modules) (U : X.Opens) (s : Γ(M,U)) : move M rfl s = s := by
  simp [move]
lemma move_map {M N : X.Modules} (a : M ⟶ N) {U V : X.Opens} (h : U = V) (s : Γ(M,U)) :
    move N h (a.app U s) = a.app V (move M h s) := by
  subst V
  simp only [move_refl]
lemma move_unit (f : X ⟶ Y) (M : Y.Modules) {U V : Y.Opens} (h : U = V) (s : Γ(M,U)) :
    move ((Scheme.Modules.pullback f).obj M) (congrArg (fun W => f ⁻¹ᵁ W) h)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U s) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app V (move M h s) := by
  subst V
  simp only [move_refl]
lemma move_move (M : X.Modules) {U V W : X.Opens} (h : U = V) (k : V = W) (s : Γ(M,U)) :
    move M k (move M h s) = move M (h.trans k) s := by
  subst V
  subst W
  simp only [move_refl]

/-- The original geometric unit, with only a proved equality of target
opens transporting its sections. -/
@[expose] def pullTo (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (h : f ⁻¹ᵁ U = V) : Γ(M,U) →+ Γ((Scheme.Modules.pullback f).obj M,V) :=
  (move _ h).comp (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U).hom

lemma composition (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (U : Z.Opens) (V : Y.Opens) (W : X.Opens)
    (hg : g ⁻¹ᵁ U = V) (hf : f ⁻¹ᵁ V = W) (hfg : (f ≫ g) ⁻¹ᵁ U = W) (s : Γ(M,U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app W
      (pullTo f ((Scheme.Modules.pullback g).obj M) V W hf (pullTo g M U V hg s)) =
        pullTo (f ≫ g) M U W hfg s := by
  change ((Scheme.Modules.pullbackComp f g).hom.app M).app W
    (move _ hf (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).app V
      (move _ hg (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U s)))) = _
  rw [← move_unit,move_move,← move_map]
  rw [OriginalUnitOpenFunctoriality318.composition]
  rfl

lemma congr {f g : X ⟶ Y} (e : f = g) (M : Y.Modules) (U : Y.Opens) (V : X.Opens)
    (hf : f ⁻¹ᵁ U = V) (hg : g ⁻¹ᵁ U = V) (s : Γ(M,U)) :
    ((Scheme.Modules.pullbackCongr e).hom.app M).app V (pullTo f M U V hf s) =
      pullTo g M U V hg s := by
  subst g
  simpa only [Scheme.Modules.pullbackCongr,eqToIso_refl,Iso.refl_hom,NatTrans.id_app]
lemma change_opens (f : X ⟶ Y) (M : Y.Modules)
    (U U' : Y.Opens) (V V' : X.Opens)
    (h : f ⁻¹ᵁ U = V) (h' : f ⁻¹ᵁ U' = V') (e : U = U') (e' : V = V') (s : Γ(M,U)) :
    move ((Scheme.Modules.pullback f).obj M) e' (pullTo f M U V h s) =
      pullTo f M U' V' h' (move M e s) := by
  subst U'
  subst V'
  simp only [move_refl]
end OriginalSectionTransport318
