module
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public section
noncomputable section

namespace OriginalR47CurveFibreFiniteBad318

open Set Order TopologicalSpace TopologicalSpace.IrreducibleCloseds

variable {T : Type*} [TopologicalSpace T] [T0Space T]

private def pointClosure (x : T) : IrreducibleCloseds T :=
  ⟨closure ({x} : Set T),isIrreducible_singleton.closure,isClosed_closure⟩

/-- In true fibre dimension at most one, any nongeneric point is
closed. Otherwise the three literal closures of its specialization,
itself, and its irreducible component give length at least two. -/
theorem closed_of_nongeneric (hDim : topologicalKrullDim T ≤ 1)
    (x : T) (hx : x ∉ genericPoints T) : IsClosed ({x} : Set T) := by
  apply isClosed_of_closure_subset
  intro y hy
  by_contra hne
  let A := pointClosure y
  let B := pointClosure x
  let C : IrreducibleCloseds T :=
    ⟨irreducibleComponent x,isIrreducible_irreducibleComponent,isClosed_irreducibleComponent⟩
  have hAB : A < B := lt_of_le_of_ne (closure_minimal
    (Set.singleton_subset_iff.mpr hy) isClosed_closure) (fun h =>
      hne (Set.mem_singleton_iff.mpr
        ((inseparable_iff_closure_eq).mpr
          (congrArg (fun D : IrreducibleCloseds T => (D : Set T)) h)).eq))
  have hBC : B < C := lt_of_le_of_ne (closure_minimal
    (Set.singleton_subset_iff.mpr mem_irreducibleComponent) isClosed_irreducibleComponent)
    (fun h => hx (show closure ({x} : Set T) ∈ irreducibleComponents T from
      (congrArg (fun D : IrreducibleCloseds T => (D : Set T)) h).symm ▸
        irreducibleComponent_mem_irreducibleComponents x))
  have h₁ : (1 : ℕ∞) ≤ Order.height B := calc
    1 = 0 + 1 := by rw [zero_add]
    _ ≤ Order.height A + 1 := add_le_add_right (zero_le _) _
    _ ≤ _ := Order.height_add_one_le hAB
  have h₂ : (2 : ℕ∞) ≤ Order.height C := calc
    (2 : ℕ∞) = 1 + 1 := by norm_num
    _ ≤ Order.height B + 1 := add_le_add_right h₁ _
    _ ≤ _ := Order.height_add_one_le hBC
  have h₃ : (2 : WithBot ℕ∞) ≤ topologicalKrullDim T :=
    (WithBot.coe_le_coe.mpr h₂).trans (Order.height_le_krullDim C)
  exact (by decide : ¬ (2 : WithBot ℕ∞) ≤ 1) (h₃.trans hDim)

variable [NoetherianSpace T] [QuasiSober T]

/-- The actual relative nonsmooth locus in a nodal field fibre has
finitely many points as soon as the fibre has dimension at most one
and is nonsingular at the generic points of its components. There
is no node enumeration or finite-scheme instance in the hypotheses. -/
theorem finite (hDim : topologicalKrullDim T ≤ 1)
    (D : Set T) (hD : IsClosed D) (hf : ∀ x ∈ D, x ∉ genericPoints T) : D.Finite := by
  obtain ⟨S,hSf,hSc,hSi,hSU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hD
  rw [hSU]
  apply hSf.sUnion
  intro C hC
  obtain ⟨x,hx⟩ := QuasiSober.sober (hSi C hC) (hSc C hC)
  have hxd : x ∈ D := hSU.symm ▸ Set.mem_sUnion_of_mem hx.mem hC
  have hc : IsClosed ({x} : Set T) := closed_of_nongeneric hDim x (hf x hxd)
  have he : ({x} : Set T) = C := hc.closure_eq.symm.trans hx.closure_eq
  rw [← he]
  exact Set.finite_singleton _

end OriginalR47CurveFibreFiniteBad318

#print axioms OriginalR47CurveFibreFiniteBad318.closed_of_nongeneric
#print axioms OriginalR47CurveFibreFiniteBad318.finite
