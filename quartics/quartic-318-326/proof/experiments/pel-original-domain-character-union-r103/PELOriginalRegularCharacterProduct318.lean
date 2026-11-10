module
public import PELOriginalCharacterDeck318
public import PELOriginalManuscriptNormalization318
public section
noncomputable section
namespace PELOriginalRegularCharacterProduct318
open Set
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalBranchLabels318
open PELStabilizerLocusInvariant318

abbrev SourceFiber (q:MaximalBase):={x:UnlevelledBase // projection x=q}
abbrev CharacterFiber (q:MaximalBase) (i:Fin 4):={x:CharacterBase i // toMaximal i x=q}
@[expose] def tuple (q:MaximalBase) (x:SourceFiber q) : ∀i,CharacterFiber q i:=
  fun i=>⟨toCharacter i x.val,x.property⟩

lemma regular_stabilizer (x:UnlevelledBase) (hx:projection x∉branchImage)
    (g:Labels) (hg:g • x=x) : g=1 := by
  by_contra h
  apply hx
  apply (branch_image_iff x).mpr
  refine ⟨Multiplicative.toAdd g,?_,hg⟩
  intro hz
  exact h (congrArg Multiplicative.ofAdd hz)

/-- The actual four prime characters jointly separate the entire
ORIGINAL generic sixteen-point fiber. The unramified hypothesis is
essential: this statement is NOT extended to branch fibers. -/
theorem tuple_injective (q:MaximalBase) (hq:q∉branchImage) :
    Function.Injective (tuple q) := by
  intro x y h
  obtain ⟨g,hg⟩:=(projection_eq_iff x.val y.val).mp (x.property.trans y.property.symm)
  have hχ:∀i,character i g=1:=by
    intro i
    have hi:toCharacter i (g • y.val)=toCharacter i y.val:=by
      rw [hg]
      exact congrArg Subtype.val (congrFun h i)
    obtain ⟨k,hk,hki⟩:=(stabilizer_character i g y.val).mp hi
    have hk1:=regular_stabilizer y.val (y.property.symm ▸ hq) k hk
    rw [hk1,map_one] at hki
    exact hki.symm
  have hg1:g=1:=by
    have hv:Multiplicative.toAdd g=(0:InertiaLabels318.V):=by
      funext i
      exact congrArg Multiplicative.toAdd (hχ i)
    exact congrArg Multiplicative.ofAdd hv
  apply Subtype.ext
  simpa only [hg1,one_smul] using hg.symm

/-- Every compatible tuple of actual intermediate points is produced by
ONE original label word acting on ONE original source point. Independent
choices of four unrelated lifts are not substituted for a source point. -/
theorem tuple_surjective (q:MaximalBase) : Function.Surjective (tuple q) := by
  intro y
  obtain ⟨x,hx⟩:=projection_surjective q
  let v:InertiaLabels318.V:=fun i=>if (y i).val=toCharacter i x then 0 else 1
  let g:Labels:=Multiplicative.ofAdd v
  have hgq:projection (g • x)=q:=
    ((projection_eq_iff _ _).mpr ⟨g,rfl⟩).trans hx
  refine ⟨⟨g • x,hgq⟩,?_⟩
  funext i
  apply Subtype.ext
  change toCharacter i (g • x)=(y i).val
  by_cases he:(y i).val=toCharacter i x
  · have hc:character i g=character i 1:=by
      simp [character,g,v,he]
    simpa only [one_smul,he] using same_character i g 1 x hc
  · have hym:(y i).val∈{z:CharacterBase i | toMaximal i z=projection x}:=by
      change toMaximal i (y i).val=projection x
      exact (y i).property.trans hx.symm
    rw [full_fiber_pair] at hym
    rcases hym with hy|hy
    · exact False.elim (he hy)
    · have hc:character i g=character i (toggle i):=by
        simp [character,g,v,toggle,he]
      exact (same_character i g (toggle i) x hc).trans hy.symm

/-- Exact fiber product equivalence only over the genuine regular base.
Normalization at ramified fibers remains a distinct geometric step. -/
@[expose] def regularEquiv (q:MaximalBase) (hq:q∉branchImage) :
    SourceFiber q≃(∀i,CharacterFiber q i):=
  Equiv.ofBijective (tuple q) ⟨tuple_injective q hq,tuple_surjective q⟩
end PELOriginalRegularCharacterProduct318
