module
public import OriginalR47TraitRoundKernel318
public section

namespace OriginalR47TraitRoundActualFibre318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47TraitRoundKernel318 (base Yp a b forgetMap restricted pullback_round)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] (p : Ideal R) [p.IsPrime]
variable {X S : Scheme.{u}} (s : X ⟶ base (R:=R)) (π : S ⟶ X)

/-- Every actual point in the old fibre is hit by the same whole
arithmetic pullback, with the specified localized base point. -/
theorem full_fibre (t : restricted p s) (z : S)
    (hz : π z = forgetMap p s t) :
    ∃ u : Yp p s π, b p s π u = z ∧ a p s π u = t :=
  Scheme.exists_preimage_of_isPullback (pullback_round p s π) z t hz

/-- An actual survivor is closed on the given global round when its
image lies over a closed old centre. Localization does not discard
any specialization in that entire closed old fibre. -/
theorem child_closed (u : Yp p s π) (hu : IsClosed ({u} : Set (Yp p s π)))
    (hbase : IsClosed ({π (b p s π u)} : Set X)) :
    IsClosed ({b p s π u} : Set S) := by
  apply isClosed_of_closure_subset
  intro z hz
  have hB : b p s π u ⤳ z := specializes_iff_mem_closure.mpr hz
  have hOld : π z = π (b p s π u) :=
    Set.mem_singleton_iff.mp ((hB.map π.continuous).mem_closed hbase (by simp))
  have hSquare : π (b p s π u) = forgetMap p s (a p s π u) := by
    have he := congrArg (fun k : Yp p s π ⟶ X => k u) (pullback_round p s π).w
    simpa only [Scheme.Hom.comp_apply] using he
  obtain ⟨v, hv, _⟩ := full_fibre p s π (a p s π u) z (hOld.trans hSquare)
  let : IsPreimmersion (b p s π) := OriginalR47TraitRoundKernel318.b_preimmersion p s π
  have hv' : b p s π u ⤳ b p s π v := hv.symm ▸ hB
  have hUV := ((b p s π).isEmbedding.isInducing.specializes_iff).mp hv'
  have heq : v = u := Set.mem_singleton_iff.mp (hUV.mem_closed hu (by simp))
  exact Set.mem_singleton_iff.mpr (hv.symm.trans (congrArg (b p s π) heq))

end OriginalR47TraitRoundActualFibre318

#print axioms OriginalR47TraitRoundActualFibre318.full_fibre
#print axioms OriginalR47TraitRoundActualFibre318.child_closed
