module
public import PELOriginalKernelRelationMap318
public section
noncomputable section
namespace PELOriginalKernelRelationIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalProductChartCover318
open PELOriginalSchemePointGroup318 PELOriginalTorsionKernelScheme318
open PELOriginalKernelRelationMap318
variable (τ : ℂ) (hτ : 0 < τ.im) (n : ℤ)

/-- The full relation map is a monomorphism on arbitrary scheme tests.
Cancellation takes place in the genuine represented point group and then
through the actual kernel closed immersion. -/
lemma hom_injective {T : Scheme} (p q : T ⟶ Product τ hτ n)
    (hpq : p≫forward τ hτ n=q≫forward τ hτ n) : p=q := by
  have hx : p≫pullback.snd (structureMap τ hτ n) (π τ hτ)=
      q≫pullback.snd (structureMap τ hτ n) (π τ hτ) := by
    have he := congrArg (fun k => k≫pullback.snd _ _) hpq
    simpa only [Category.assoc,forward_second] using he
  let ρ := p≫productBase τ hτ n
  have hq : q≫productBase τ hτ n=ρ := by
    change q≫(pullback.snd _ _≫π τ hτ)=p≫(pullback.snd _ _≫π τ hτ)
    rw [←Category.assoc,←Category.assoc,hx]
  let Fp := pull τ hτ (productBase τ hτ n) p (rfl : p≫productBase τ hτ n=ρ)
  let Fq := pull τ hτ (productBase τ hτ n) q hq
  have hs : Fp (secondPoint τ hτ n)=Fq (secondPoint τ hτ n) := by
    apply Subtype.ext
    exact hx
  have ha : Fp (firstPoint τ hτ n)+Fp (secondPoint τ hτ n)=
      Fq (firstPoint τ hτ n)+Fq (secondPoint τ hτ n) := by
    rw [←map_add,←map_add]
    apply Subtype.ext
    have he := congrArg (fun k => k≫pullback.fst _ _) hpq
    simpa only [Category.assoc,forward_first] using he
  rw [hs] at ha
  have hk := add_right_cancel ha
  apply pullback.hom_ext
  · apply (cancel_mono (inclusion τ hτ n)).mp
    have he := congrArg Subtype.val hk
    change p≫(pullback.fst _ _≫inclusion τ hτ n)=
      q≫(pullback.fst _ _≫inclusion τ hτ n) at he
    simpa only [Category.assoc] using he
  · exact hx

/-- Genuine whole-scheme torsor relation, not only a fiber cardinality:
K_n × A is isomorphic to A ×_[n],A A through (k,x)↦(k+x,x). -/
@[expose] def iso : Product τ hτ n ≅ Relation τ hτ n := by
  let q := (lift_point τ hτ n (𝟙 (Relation τ hτ n)) (Category.id_comp _)).choose
  have hq := (lift_point τ hτ n (𝟙 (Relation τ hτ n)) (Category.id_comp _)).choose_spec
  refine ⟨forward τ hτ n,q,?_,hq⟩
  apply hom_injective τ hτ n
  rw [Category.assoc,hq,Category.comp_id,Category.id_comp]
lemma iso_forward : (iso τ hτ n).hom=forward τ hτ n := rfl
@[reassoc] lemma iso_second : (iso τ hτ n).hom≫pullback.snd _ _=pullback.snd _ _ := by
  rw [iso_forward,forward_second]
end PELOriginalKernelRelationIso318
