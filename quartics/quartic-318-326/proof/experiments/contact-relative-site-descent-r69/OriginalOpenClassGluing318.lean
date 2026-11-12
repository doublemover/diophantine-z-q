module
public import OriginalPointedOpenTransitions318
public section
noncomputable section
namespace OriginalOpenClassGluing318
open AlgebraicGeometry CategoryTheory TopologicalSpace LineSheafClass318
open RelativeLineClassBaseChange318 RelativeLineClassQuotient318 RigidifiedRelativeClass318
open OriginalOpenFamilyTest318 OriginalPointedOpenFamily318
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {C B T : Scheme.{u}} (q : C ⟶ B) (b : T ⟶ B) (e : B ⟶ C) (hs : e ≫ q = 𝟙 B)
  {ι : Type u} (U : ι → T.Opens) (hc : (⊤ : T.Opens) ≤ iSup U)
  (c : ∀ i, RelativeClass (projection q b ∣_ U i))
  (he : ∀ V : T.Opens, Function.Bijective (sec q b e hs V).appTop)
  (matching : ∀ i j,
    OriginalPointedOpenFamily318.classMap q b (show U i ⊓ U j ≤ U i from inf_le_left) (c i) =
      OriginalPointedOpenFamily318.classMap q b (show U i ⊓ U j ≤ U j from inf_le_right) (c j))

abbrev representative (i : ι) := RigidifiedClassQuotient318.representative (sec q b e hs (U i))
  (projection q b ∣_ U i) (section_projection q b (U i) e hs) (c i)

include hc in
lemma source_cover : (⊤ : (family q b).Opens) ≤ iSup (fun i => sourceOpen q b (U i)) := by
  intro x hx
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (hc (show projection q b x ∈ (⊤ : T.Opens) from trivial))
  exact Opens.mem_iSup.mpr ⟨i,hi⟩

@[expose] def data : LocalChartTransition318.Data (fun i => sourceOpen q b (U i))
    (fun i => (representative q b e hs U c i).line.object) :=
  OriginalPointedOpenTransitions318.data q b e hs U (representative q b e hs U c) he (by
    intro i j
    rw [RigidifiedClassQuotient318.representative_class,RigidifiedClassQuotient318.representative_class]
    exact matching i j)

/-- Actual original line on the full family obtained by gluing the
unchanged local representative lines and their rigidity-derived transitions. -/
@[expose] def line : Line (family q b) :=
  LocalLineOpenDescent318.line (fun i => sourceOpen q b (U i))
    (fun i => (representative q b e hs U c i).line) (data q b e hs U c he matching)
    (source_cover q b U hc)

@[expose] def comparison (i : ι) :
    (Scheme.Modules.pullback (sourceOpen q b (U i)).ι).obj (line q b e hs U hc c he matching).object ≅
      (representative q b e hs U c i).line.object :=
  ((Scheme.Modules.restrictFunctorIsoPullback (sourceOpen q b (U i)).ι).app
      (line q b e hs U hc c he matching).object).symm ≪≫
    LocalLineOpenDescent318.comparison (fun i => sourceOpen q b (U i))
      (fun i => (representative q b e hs U c i).line) (data q b e hs U c he matching)
      (source_cover q b U hc) i

@[expose] def descendedClass : TestClass q b :=
  RelativeLineClassQuotient318.classMap (projection q b) (classOf (line q b e hs U hc c he matching))

lemma restriction_class (i : ι) :
    OriginalOpenRelativeClasses318.restriction q b (U i) (descendedClass q b e hs U hc c he matching) = c i := by
  have hh := congrArg (RelativeLineClassQuotient318.classMap (projection q b ∣_ U i))
    (LineSheafClass318.classOf_eq (comparison q b e hs U hc c he matching i))
  change OriginalOpenRelativeClasses318.restriction q b (U i) (descendedClass q b e hs U hc c he matching) =
    relativeClass (projection q b ∣_ U i) (sec q b e hs (U i)) (representative q b e hs U c i) at hh
  exact hh.trans (RigidifiedClassQuotient318.representative_class _ _ _ _)

include hc he matching in
/-- Arbitrary matching original relative classes on the actual inverse-image
open cover glue to an actual global relative class, without affine assumptions. -/
theorem effective : ∃ d : TestClass q b, ∀ i, OriginalOpenRelativeClasses318.restriction q b (U i) d = c i :=
  ⟨descendedClass q b e hs U hc c he matching,restriction_class q b e hs U hc c he matching⟩
end OriginalOpenClassGluing318
