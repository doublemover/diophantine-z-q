module
public import FourRootNormalizedPointCharts318
public section
noncomputable section
namespace FourRootNormalizedOverlap318
open Set Topology FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ)

lemma toInfinity_continuous : Continuous (toInfinity b) := by
  have hz (k:Fin 4) : Continuous (fun p:FiniteOverlap b=>p.val.val.2 k):=
    (continuous_apply k).comp continuous_subtype_val.subtype_val.snd
  have hu:Continuous (fun p:FiniteOverlap b=>(p.val.val.2 0)⁻¹):=
    (hz 0).inv₀ (fun p=>p.property)
  have hs:Continuous (fun p:FiniteOverlap b=>fun k=>p.val.val.2 k/p.val.val.2 0):=
    continuous_pi (fun k=>(hz k).div (hz 0) (fun p=>p.property))
  exact ((hu.prodMk hs).subtype_mk _).subtype_mk _

lemma toFinite_continuous : Continuous (toFinite b) := by
  have hu:Continuous (fun p:InfinityOverlap b=>p.val.val.1):=
    continuous_subtype_val.subtype_val.fst
  have hs (k:Fin 4) : Continuous (fun p:InfinityOverlap b=>p.val.val.2 k):=
    (continuous_apply k).comp continuous_subtype_val.subtype_val.snd
  have ht:Continuous (fun p:InfinityOverlap b=>b 0+(p.val.val.1^2)⁻¹):=
    continuous_const.add ((hu.pow 2).inv₀ (fun p=>pow_ne_zero 2 p.property))
  have hz:Continuous (fun p:InfinityOverlap b=>fun k=>p.val.val.2 k/p.val.val.1):=
    continuous_pi (fun k=>(hs k).div hu (fun p=>p.property))
  exact ((ht.prodMk hz).subtype_mk _).subtype_mk _

/-- The gluing transition is a genuine homeomorphism in the independent
inherited complex-coordinate topologies, not a topology transported from
our original source curve. -/
@[expose] def overlapHomeomorph : FiniteOverlap b≃ₜInfinityOverlap b where
  toEquiv:=overlapEquiv b
  continuous_toFun:=toInfinity_continuous b
  continuous_invFun:=toFinite_continuous b

lemma finite_overlap_open : IsOpen {p:FinitePoints b|p.val.2 0≠0}:=by
  have hc : Continuous (fun p : FinitePoints b => p.val.2 (0 : Fin 4)) :=
    (continuous_apply (0 : Fin 4)).comp continuous_subtype_val.snd
  exact (isClosed_singleton : IsClosed ({0} : Set ℂ)).isOpen_compl.preimage hc
lemma infinity_overlap_open : IsOpen {p:InfinityPoints b|p.val.1≠0}:=
  (isClosed_singleton : IsClosed ({0} : Set ℂ)).isOpen_compl.preimage
    continuous_subtype_val.fst

/-- Exactly eight infinity points, enumerated by the three retained
signs. There is NO quotient by simultaneous sign after z0 normalization. -/
@[expose] def signs (v:Fin 3→Bool) : InfinitySigns:=
  ⟨Fin.cases 1 (fun j=>if v j then 1 else -1),by rfl,by
    intro k
    refine Fin.cases ?_ (fun j=>?_) k
    · norm_num
    · cases hv:v j <;> norm_num [Fin.cases,hv]⟩
@[expose] def bits (s:InfinitySigns) (j:Fin 3):Bool:=decide (s.val j.succ=1)
lemma bits_signs (v:Fin 3→Bool) : bits (signs v)=v := by
  funext j
  cases h:v j <;> norm_num [bits,signs,h]
lemma signs_bits (s:InfinitySigns) : signs (bits s)=s := by
  apply Subtype.ext
  funext k
  refine Fin.cases ?_ (fun j=>?_) k
  · exact s.property.1.symm
  · have hh:s.val j.succ=1 ∨ s.val j.succ= -1:=
      sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa using s.property.2 j.succ)
    rcases hh with h|h <;> norm_num [signs,bits,h]
@[expose] def signEquiv : (Fin 3→Bool)≃InfinitySigns where
  toFun:=signs
  invFun:=bits
  left_inv:=bits_signs
  right_inv:=signs_bits
lemma infinity_card : Nat.card InfinitySigns=8 := by
  rw [←Nat.card_congr signEquiv]
  norm_num [Nat.card_eq_fintype_card]
end FourRootNormalizedOverlap318
