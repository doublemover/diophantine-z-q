module
public import CuspSeparation318
public section
noncomputable section
open Function Filter Topology TopologicalSpace GammaOneFiber318
open PeterssonQuotient318 ActualSingleCusp318
namespace FilledCuspHausdorff318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

theorem old_or_cusp (N:ℕ) (z:Filled N) :
    (∃b,original N b=z) ∨ z=cusp N := by
  by_cases hz:z=cusp N
  · exact Or.inr hz
  · exact Or.inl ((Set.ext_iff.mp (range_original N) z).mpr hz)

theorem separate_old (N:ℕ) (b c:Base (image N)) (hbc:b≠c) :
    ∃U V:Set (Filled N),IsOpen U ∧ IsOpen V ∧
      original N b∈U ∧ original N c∈V ∧ Disjoint U V := by
  obtain ⟨U,V,hU,hV,hb,hc,hdis⟩:=t2_separation hbc
  refine ⟨original N '' U,original N '' V,
    (original_isOpenEmbedding N).isOpenMap _ hU,(original_isOpenEmbedding N).isOpenMap _ hV,
    ⟨b,hb,rfl⟩,⟨c,hc,rfl⟩,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
  have hyx:y=x := (original_isOpenEmbedding N).injective he
  subst y
  exact Set.disjoint_left.mp hdis hx hy

/-- The genuine one-cusp gluing is Hausdorff. This is proved from actual
j-growth; it is not a generic, false inference from gluing open subspaces. -/
theorem filled_t2 (N:ℕ) (hN:5≤N) : T2Space (Filled N) := by
  constructor
  intro x y hxy
  rcases old_or_cusp N x with ⟨b,rfl⟩ | rfl
  · rcases old_or_cusp N y with ⟨c,rfl⟩ | rfl
    · exact separate_old N b c (fun he=>hxy (congrArg (original N) he))
    · exact CuspSeparation318.separate_cusp N hN b
  · rcases old_or_cusp N y with ⟨c,rfl⟩ | rfl
    · obtain ⟨U,V,hU,hV,hc,hcu,hd⟩:=CuspSeparation318.separate_cusp N hN c
      exact ⟨V,U,hV,hU,hcu,hc,hd.symm⟩
    · exact False.elim (hxy rfl)

end FilledCuspHausdorff318
