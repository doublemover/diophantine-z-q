module
public import PELOriginalRegularLegendreHomeomorph318
public import NormalizedLegendreAllFibers318
public section
noncomputable section
namespace PELOriginalCompletedLegendreBijection318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalFourBranchCoordinate318 PELOriginalRegularCoverPatches318
open PELOriginalGluedLegendreMap318 PELOriginalGluedLegendreFibers318
open NormalizedLegendreFieldPoints318

abbrev Completed (i:Fin 4):=Option (FinitePoints (branchParameter i))
@[expose] def Branch (i:Fin 4) (q:OnePoint ℂ) : Prop:=
  q=∞ ∨ q=(0:ℂ) ∨ q=(1:ℂ) ∨ q=(branchParameter i:ℂ)
lemma regular_iff (i:Fin 4) (x:CharacterBase i) :
    x∈Regular i ↔ ¬Branch i (normalizedMap i x) := by
  constructor
  · rintro ⟨z,hz,h0,h1,hλ⟩
    rw [hz]
    simp only [Branch,OnePoint.coe_ne_infty,OnePoint.coe_eq_coe,false_or]
    exact not_or.mpr ⟨h0,not_or.mpr ⟨h1,hλ⟩⟩
  · intro hn
    obtain ⟨z,hz⟩:=OnePoint.ne_infty_iff_exists.mp
      (show normalizedMap i x≠∞ from fun h=>hn (Or.inl h))
    refine ⟨z,hz.symm,?_,?_,?_⟩
    · intro h;apply hn;exact Or.inr (Or.inl (hz.symm.trans (congrArg ((↑):ℂ→OnePoint ℂ) h)))
    · intro h;apply hn;exact Or.inr (Or.inr (Or.inl (hz.symm.trans (congrArg ((↑):ℂ→OnePoint ℂ) h))))
    · intro h;apply hn;exact Or.inr (Or.inr (Or.inr (hz.symm.trans (congrArg ((↑):ℂ→OnePoint ℂ) h))))

/-- At an actual original branch value the WHOLE source fiber has one
point. This cardinality is consumed only for the exceptional points,
never as a substitute for the regular geometric cover comparison. -/
lemma source_branch_unique (i:Fin 4) (q:OnePoint ℂ) (hq:Branch i q)
    (x y:CharacterBase i) (hx:normalizedMap i x=q) (hy:normalizedMap i y=q) : x=y := by
  let F:Type:={p:CharacterBase i//normalizedMap i p=q}
  have hc:Nat.card F=1:=by
    rw [show Nat.card F=Nat.card {p:CharacterBase i//normalizedMap i p=q} from rfl,
      all_fibers,if_pos hq]
  letI : Finite F:=Nat.finite_of_card_ne_zero (by rw [hc];decide)
  letI : Fintype F:=Fintype.ofFinite F
  obtain ⟨p,hp⟩:=Fintype.card_eq_one_iff.mp (show Fintype.card F=1 by rw [←Nat.card_eq_fintype_card,hc])
  exact congrArg Subtype.val ((hp (⟨x,hx⟩:F)).trans (hp (⟨y,hy⟩:F)).symm)

lemma target_branch_unique (i:Fin 4) (q:OnePoint ℂ) (hq:Branch i q)
    (x y:Completed i)
    (hx:NormalizedLegendreWholeProjection318.coordinate (branchParameter i) x=q)
    (hy:NormalizedLegendreWholeProjection318.coordinate (branchParameter i) y=q) : x=y := by
  have hf:NormalizedLegendreWholeProjection318.deck (branchParameter i) x=x:=
    (NormalizedLegendreWholeProjection318.fixed_iff_branch _ x).mpr (hx.symm ▸ hq)
  rcases (NormalizedLegendreWholeProjection318.same_coordinate _ x y).mp (hx.trans hy.symm) with he|he
  · exact he
  · rwa [hf] at he

/-- A set-theoretic section used ONLY at singleton branch fibers. Its
nonbranch values are irrelevant; no continuity of algebraic root choice
is ever claimed or used. -/
@[expose] def branchPoint (i:Fin 4) : OnePoint ℂ→Completed i :=
  OnePoint.rec none (fun z=>some (NormalizedLegendreAllFibers318.point (branchParameter i) z))
lemma branchPoint_projection (i:Fin 4) (q:OnePoint ℂ) :
    NormalizedLegendreWholeProjection318.coordinate (branchParameter i) (branchPoint i q)=q := by
  induction q using OnePoint.rec with
  | infty=>rfl
  | coe z=>rfl

/-- Fixed completed candidate: the ACTUAL regular glued map on its whole
locus, and the forced unique actual target point on each branch fiber. -/
@[expose] def completedMap (i:Fin 4) (x:CharacterBase i) : Completed i:=
  if h:x∈Regular i then some (finiteMap i ⟨x,h⟩) else branchPoint i (normalizedMap i x)
lemma completedMap_regular (i:Fin 4) (x:Regular i) :
    completedMap i x.val=some (finiteMap i x) := by
  simp only [completedMap,dif_pos x.property]
lemma completed_projection (i:Fin 4) (x:CharacterBase i) :
    NormalizedLegendreWholeProjection318.coordinate (branchParameter i) (completedMap i x)=normalizedMap i x := by
  unfold completedMap
  split with h
  · exact coordinates_projection i x h
  · exact branchPoint_projection i _
lemma completedMap_branch (i:Fin 4) (x:CharacterBase i) (hq:Branch i (normalizedMap i x))
    (y:Completed i) (hy:NormalizedLegendreWholeProjection318.coordinate (branchParameter i) y=normalizedMap i x) :
    completedMap i x=y:=target_branch_unique i _ hq _ _ (completed_projection i x) hy

lemma completedMap_injective (i:Fin 4) : Function.Injective (completedMap i) := by
  intro x y h
  have hp:normalizedMap i x=normalizedMap i y:=by
    rw [←completed_projection i x,←completed_projection i y,h]
  by_cases hx:x∈Regular i
  · have hy:y∈Regular i:=(regular_iff i y).mpr (hp ▸ (regular_iff i x).mp hx)
    have hh:some (finiteMap i ⟨x,hx⟩)=some (finiteMap i ⟨y,hy⟩):=by
      rw [←completedMap_regular,←completedMap_regular]
      exact h
    exact congrArg Subtype.val (finiteMap_injective i (Option.some.inj hh))
  · have hb:Branch i (normalizedMap i x):=not_not.mp (fun hn=>hx ((regular_iff i x).mpr hn))
    exact source_branch_unique i _ hb x y rfl hp.symm

lemma completedMap_surjective (i:Fin 4) : Function.Surjective (completedMap i) := by
  intro p
  let q:=NormalizedLegendreWholeProjection318.coordinate (branchParameter i) p
  by_cases hb:Branch i q
  · obtain ⟨x,hx⟩:=PELOriginalNormalizedDoubleCover318.surjective i q
    exact ⟨x,target_branch_unique i q hb _ p ((completed_projection i x).trans hx) rfl⟩
  · cases p with
    | none=>exact False.elim (hb (Or.inl rfl))
    | some p=>
      have hr:p.val.1≠0 ∧ p.val.1≠1 ∧ p.val.1≠branchParameter i:=by
        change ¬Branch i (p.val.1:OnePoint ℂ) at hb
        simpa only [Branch,OnePoint.coe_ne_infty,OnePoint.coe_eq_coe,false_or,not_or] using hb
      obtain ⟨x,hx⟩:=comparison_surjective i (⟨p,hr⟩:Target i)
      refine ⟨x.val,?_⟩
      rw [completedMap_regular]
      exact congrArg some (congrArg Subtype.val hx)

/-- This is a full point equivalence with the actual completed Legendre
scheme-point model. Continuity and completed-atlas holomorphy still need
the genuine local branch extension, and are NOT asserted by this theorem. -/
@[expose] def completedEquiv (i:Fin 4) : CharacterBase i≃Completed i:=
  Equiv.ofBijective (completedMap i) ⟨completedMap_injective i,completedMap_surjective i⟩
lemma completed_scheme_projection (i:Fin 4) (x:CharacterBase i) :
    NormalizedLegendreFiniteProjection318.project (branchParameter i)
      (schemeEquiv (branchParameter i) (completedMap i x))=
        PELOriginalCommonLegendreBase318.originalProjection i x := by
  rw [NormalizedLegendreWholeProjection318.whole_projection,
    PELOriginalCommonLegendreBase318.original_projection_coordinate,completed_projection]
end PELOriginalCompletedLegendreBijection318
