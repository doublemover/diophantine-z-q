module
public import LineIsoRegularScalars318
public import LinePullbackTransitions318
public section
noncomputable section
namespace TranslatedLineIsoScalars318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (f : X ⟶ X) (M : X.Modules) {ι : Type u}
  (U : ι → X.Opens)
  (e : ∀ i,SheafOfModules.unit (U i).toScheme.ringCatSheaf ≅ M.restrict (U i).ι)
  (E : M ≅ (Scheme.Modules.pullback f).obj M)

@[expose] def domain (a : ι × ι) : X.Opens := U a.1 ⊓ f ⁻¹ᵁ U a.2
@[expose] def targetFrame (i : ι) := LinePullbackFrames318.frame f M (U i) (e i)

/-- Source and translated target charts are both genuine whole opens.
The input is an actual isomorphism to the actual module-sheaf pullback. -/
@[expose] def unit (a : ι × ι) : Γ(X,domain f U a)ˣ :=
  LineIsoRegularScalars318.scalar E (fun a : ι × ι => U a.1)
    (fun a : ι × ι => f ⁻¹ᵁ U a.2) (fun a => e a.1) (fun a => targetFrame f M U e a.2)
    a (domain f U a) inf_le_left inf_le_right

lemma covers (hU : (⊤ : X.Opens) ≤ ⨆ i,U i) : (⊤ : X.Opens) ≤ ⨆ a : ι × ι,domain f U a := by
  intro x hx
  have h1 := hU (show x∈(⊤ : X.Opens) from trivial)
  have h2 := hU (show f x∈(⊤ : X.Opens) from trivial)
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h1
  obtain ⟨j,hj⟩ := TopologicalSpace.Opens.mem_iSup.mp h2
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i,j),⟨hi,hj⟩⟩

/-- Exact target transition on a full inverse-image overlap. -/
lemma target_transition (i j : ι) :
    LineFrameTransitions318.scalar ((Scheme.Modules.pullback f).obj M)
      (fun i => f ⁻¹ᵁ U i) (targetFrame f M U e) i j (f ⁻¹ᵁ (U i ⊓ U j))
      (f.preimage_mono inf_le_left) (f.preimage_mono inf_le_right)=
    Units.map (f.app (U i ⊓ U j)).hom.toMonoidHom
      ((LineFrameCocycle318.cocycle M U e).transition i j) := by
  exact congrArg (fun C => C.transition i j) (LinePullbackTransitions318.cocycle f M U e)

/-- Every smaller source open retains the original pullback map and
original target cocycle; no equality only at closed points is used. -/
lemma target_transition_subopen (i j : ι) (W : X.Opens)
    (h : W ≤ f ⁻¹ᵁ (U i ⊓ U j)) :
    LineFrameTransitions318.scalar ((Scheme.Modules.pullback f).obj M)
      (fun i => f ⁻¹ᵁ U i) (targetFrame f M U e) i j W
      (h.trans (f.preimage_mono inf_le_left)) (h.trans (f.preimage_mono inf_le_right))=
    Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
      (Units.map (f.app (U i ⊓ U j)).hom.toMonoidHom
        ((LineFrameCocycle318.cocycle M U e).transition i j)) := by
  rw [←target_transition f M U e i j]
  exact (LineFrameTransitions318.restrict _ _ _ i j _ _ h).symm

/-- Whole regular-unit equation on the actual source/translated overlap.
The remaining analytic comparison will evaluate this equation, not
postulate a periodic scalar or a character. -/
lemma overlap (a b : ι × ι) :
    let W := domain f U a ⊓ domain f U b
    let hs : W ≤ U a.1 ⊓ U b.1 :=
      le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
    let ht : W ≤ f ⁻¹ᵁ (U a.2 ⊓ U b.2) := by
      intro x hx
      exact ⟨hx.1.2,hx.2.2⟩
    Units.map (X.presheaf.map (homOfLE (show W ≤ domain f U a from inf_le_left)).op).hom.toMonoidHom
        (unit f M U e E a) *
      Units.map (X.presheaf.map (homOfLE hs).op).hom.toMonoidHom
        ((LineFrameCocycle318.cocycle M U e).transition a.1 b.1)=
    Units.map (X.presheaf.map (homOfLE ht).op).hom.toMonoidHom
      (Units.map (f.app (U a.2 ⊓ U b.2)).hom.toMonoidHom
        ((LineFrameCocycle318.cocycle M U e).transition a.2 b.2)) *
      Units.map (X.presheaf.map (homOfLE (show W ≤ domain f U b from inf_le_right)).op).hom.toMonoidHom
        (unit f M U e E b) := by
  dsimp only
  rw [unit,unit,LineIsoRegularScalars318.restrict,LineIsoRegularScalars318.restrict]
  rw [show Units.map (X.presheaf.map (homOfLE
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))).op).hom.toMonoidHom
      ((LineFrameCocycle318.cocycle M U e).transition a.1 b.1)=
    LineFrameTransitions318.scalar M U e a.1 b.1 _ _ _ from
      LineFrameTransitions318.restrict M U e a.1 b.1 inf_le_left inf_le_right _]
  rw [←target_transition_subopen]
  exact LineIsoRegularScalars318.transition E (fun a : ι × ι => U a.1)
    (fun a : ι × ι => f ⁻¹ᵁ U a.2) (fun a => e a.1) (fun a => targetFrame f M U e a.2)
    a b _ _ _ _ _
end TranslatedLineIsoScalars318
