module
public import OriginalPointedOpenFamily318
public section
noncomputable section
namespace OriginalPointedOpenTransitions318
open AlgebraicGeometry CategoryTheory RelativeRigidifiedLine318 RigidifiedLineIsomorphism318
open RigidifiedRelativeClass318 RelativeLineClassQuotient318 OriginalOpenFamilyTest318
open OriginalPointedOpenFamily318
set_option maxHeartbeats 2600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (e : B ⟶ C) (hs : e ≫ q = 𝟙 B)
  {ι : Type u} (U : ι → T.Opens) (L : ∀ i, RigidifiedLine (sec q b e hs (U i)))
  (he : ∀ V : T.Opens, Function.Bijective (sec q b e hs V).appTop)
  (matching : ∀ i j,
    OriginalPointedOpenFamily318.classMap q b (show U i ⊓ U j ≤ U i from inf_le_left)
        (relativeClass (projection q b ∣_ U i) (sec q b e hs (U i)) (L i)) =
      OriginalPointedOpenFamily318.classMap q b (show U i ⊓ U j ≤ U j from inf_le_right)
        (relativeClass (projection q b ∣_ U j) (sec q b e hs (U j)) (L j)))

@[expose] def transition (i j : ι) : CompatibleIso (sec q b e hs (U i ⊓ U j))
    (line q b e hs (show U i ⊓ U j ≤ U i from inf_le_left) (L i))
    (line q b e hs (show U i ⊓ U j ≤ U j from inf_le_right) (L j)) :=
  RigidifiedIsoCoherence318.transition (sec q b e hs (U i ⊓ U j))
    (projection q b ∣_ (U i ⊓ U j)) (section_projection q b (U i ⊓ U j) e hs)
    (he _) (by rw [line_class,line_class]; exact matching i j)

@[expose] def edge (i j : ι) (V : T.Opens) (h : V ≤ U i ⊓ U j) :
    CompatibleIso (sec q b e hs V)
      (line q b e hs (h.trans inf_le_left) (L i))
      (line q b e hs (h.trans inf_le_right) (L j)) :=
  RigidifiedIsoCoherence318.compose _
    (RigidifiedIsoCoherence318.inverse _ (composition q b e hs inf_le_left h (L i)))
    (RigidifiedIsoCoherence318.compose _
      (mapIso q b e hs h (transition q b e hs U L he matching i j))
      (composition q b e hs inf_le_right h (L j)))

lemma edge_iso (i j : ι) (V : T.Opens) (h : V ≤ U i ⊓ U j) :
    (edge q b e hs U L he matching i j V h).iso =
      LocalChartTransition318.edge (fun i => sourceOpen q b (U i)) (fun i => (L i).line.object)
        (transition q b e hs U L he matching i j).iso (sourceOpen q b V)
        ((projection q b).preimage_mono h) := by
  simp only [edge,RigidifiedIsoCoherence318.compose,RigidifiedIsoCoherence318.inverse,
    composition_iso,LocalChartTransition318.edge] <;> rfl

/-- The original Fi-only open gluing data, with identity and the whole
triple equation derived from actual section rigidity, not supplied. -/
@[expose] def data : LocalChartTransition318.Data (fun i => sourceOpen q b (U i))
    (fun i => (L i).line.object) where
  transition i j := (transition q b e hs U L he matching i j).iso
  identity i := by
    have hh := compatible_unique (sec q b e hs (U i ⊓ U i)) (he _).injective _ _
      (transition q b e hs U L he matching i i) (RigidifiedIsoCoherence318.identity _ _)
    exact congrArg (fun a => a.iso) hh
  cocycle i j k := by
    have hh := compatible_unique (sec q b e hs ((U i ⊓ U j) ⊓ U k)) (he _).injective _ _
      (RigidifiedIsoCoherence318.compose _
        (edge q b e hs U L he matching i j ((U i ⊓ U j) ⊓ U k) inf_le_left)
        (edge q b e hs U L he matching j k ((U i ⊓ U j) ⊓ U k)
          (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
      (edge q b e hs U L he matching i k ((U i ⊓ U j) ⊓ U k)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right))
    have hmap := congrArg (fun a => a.iso) hh
    change (edge q b e hs U L he matching i j ((U i ⊓ U j) ⊓ U k) inf_le_left).iso ≪≫
      (edge q b e hs U L he matching j k ((U i ⊓ U j) ⊓ U k)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right)).iso =
      (edge q b e hs U L he matching i k ((U i ⊓ U j) ⊓ U k)
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right)).iso at hmap
    simpa only [edge_iso] using hmap
end OriginalPointedOpenTransitions318
