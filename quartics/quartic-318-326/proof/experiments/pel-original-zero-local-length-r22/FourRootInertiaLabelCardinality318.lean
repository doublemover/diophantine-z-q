module
public import FourRootActualResidueInertia318
public section
noncomputable section
namespace FourRootInertiaLabelCardinality318
open FourBinaryCharacters318 FourRootNormalizedPointCharts318 FourRootActualResidueInertia318
@[expose] def word (s:Fin 4→Bool):FourBinaryCharacters318.Group:=
  fun i=>Multiplicative.ofAdd (if s i then 1 else 0)
@[expose] def signEquivalence:FourBinaryCharacters318.Group≃(Fin 4→Bool) where
  toFun:=signPattern
  invFun:=word
  left_inv g:=by
    funext i
    have two:∀x:Multiplicative (ZMod 2),x=1∨x=Multiplicative.ofAdd 1:=by decide
    rcases two (g i) with h|h <;> simp [word,signPattern,h]
  right_inv s:=by
    funext i
    cases h:s i <;> simp [word,signPattern,h]
lemma coordinate_one_iff (g:FourBinaryCharacters318.Group) (i:Fin 4):
    coordinate (F:=ℂ) i g=1 ↔ signPattern g i=false:=by
  by_cases h:Multiplicative.toAdd (g i)=0 <;> simp [coordinate,signPattern,h]
lemma coordinate_eq_iff (g:FourBinaryCharacters318.Group) (i j:Fin 4):
    coordinate (F:=ℂ) i g=coordinate (F:=ℂ) j g ↔ signPattern g i=signPattern g j:=by
  by_cases h:Multiplicative.toAdd (g i)=0 <;>
    by_cases k:Multiplicative.toAdd (g j)=0 <;> simp [coordinate,signPattern,h,k]

@[expose] def supportedEquivalence (j:Fin 4):
    {s:Fin 4→Bool // ∀i,i≠j→s i=false}≃Bool where
  toFun s:=s.val j
  invFun bit:=⟨fun i=>if i=j then bit else false,by intro i hi;simp [hi]⟩
  left_inv s:=by
    apply Subtype.ext
    funext i
    by_cases hi:i=j
    · subst i;simp
    · simpa only [if_neg hi] using (s.property i hi).symm
  right_inv bit:=by simp
@[expose] def constantEquivalence:
    {s:Fin 4→Bool // ∀i,s i=s 0}≃Bool where
  toFun s:=s.val 0
  invFun bit:=⟨fun _=>bit,fun _=>rfl⟩
  left_inv s:=by
    apply Subtype.ext
    funext i
    exact (s.property i).symm
  right_inv _:=rfl

variable (b:Fin 4→ℂ) (hb:Function.Injective b)
@[expose] def finiteLabels (p:FinitePoints b):Set FourBinaryCharacters318.Group:=
  {g|FourRootCoordinateRingSigns318.finiteEquiv b g∈
    (finitePrime b p).inertia (FourRootAffineCoordinateRing318.Ring b≃ₐ[ℂ]FourRootAffineCoordinateRing318.Ring b)}
@[expose] def infinityLabels (p:InfinityPoints b):Set FourBinaryCharacters318.Group:=
  {g|FourRootCoordinateRingSigns318.infinityEquiv b g∈
    (infinityPrime b p).inertia (FourRootInfinityCoordinateRing318.Ring b≃ₐ[ℂ]FourRootInfinityCoordinateRing318.Ring b)}

/-- Exactly two ORIGINAL deck labels lie in the actual ideal inertia at
any finite branch point; this is not yet an independent ramification-index theorem. -/
@[expose] def finiteEquivalence (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    finiteLabels b p≃Bool:=
  (signEquivalence.subtypeEquiv (fun g=>by
    change (FourRootCoordinateRingSigns318.finiteEquiv b g∈_) ↔
      ∀i,i≠j→signPattern g i=false
    rw [finite_branch_inertia b hb g j p hp]
    simp only [coordinate_one_iff])).trans (supportedEquivalence j)

@[expose] def infinityEquivalence (p:InfinityPoints b) (hp:p.val.1=0):
    infinityLabels b p≃Bool:=
  (signEquivalence.subtypeEquiv (fun g=>by
    change (FourRootCoordinateRingSigns318.infinityEquiv b g∈_) ↔
      ∀i,signPattern g i=signPattern g 0
    rw [infinity_inertia b g p hp]
    simp only [coordinate_eq_iff])).trans constantEquivalence

theorem finite_card (j:Fin 4) (p:FinitePoints b) (hp:p.val.1=b j):
    Nat.card (finiteLabels b p)=2:=by
  rw [Nat.card_congr (finiteEquivalence b hb j p hp)]
  simp
theorem infinity_card (p:InfinityPoints b) (hp:p.val.1=0):
    Nat.card (infinityLabels b p)=2:=by
  rw [Nat.card_congr (infinityEquivalence b p hp)]
  simp
end FourRootInertiaLabelCardinality318
