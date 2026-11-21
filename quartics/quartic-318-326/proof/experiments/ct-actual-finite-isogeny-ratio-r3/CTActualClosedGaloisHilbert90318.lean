module
public import CTClosedGaloisCocycleFiniteLayer318
public import CTFiniteSubgroupHilbert90318
public section
noncomputable section

namespace CTActualClosedGaloisHilbert90318

open CTClosedGaloisCocycleFiniteLayer318 CTFiniteSubgroupHilbert90318

variable (K : Type) [Field K] [CharZero K]
local notation "A" => AlgebraicClosure K
local notation "G" => (A ≃ₐ[K] A)

/-- Continuous Hilbert 90 for the actual closed subgroup with the
subspace Krull topology, proved by descending the same crossed
cochain into its genuine finite argument-and-value window. -/
theorem actual_closed_hilbert90 (I : Subgroup G) (hClosed : IsClosed (I : Set G))
    (c : I → Aˣ) (hlc : IsLocallyConstant c)
    (hc : ∀ g h : I, c (g*h)=(g : G) • c h*c g) :
    ∃ a : Aˣ, ∀ s : I, (s : G) • a / a=c s := by
  obtain ⟨L,hF,hL⟩ := finite_layer_for_closed_cocycle K I hClosed c hlc hc
  let E := L.toIntermediateField
  let Q := (E ≃ₐ[K] E)
  let q : G →* Q := restriction K L
  let J : Subgroup Q := (q.comp I.subtype).range
  let jr : I →* J := {
    toFun s := ⟨q (s:G),⟨s,rfl⟩⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' s t := Subtype.ext (map_mul q (s:G) (t:G)) }
  have hjr : Function.Surjective jr := by
    intro s
    obtain ⟨a,ha⟩ := s.property
    exact ⟨a,Subtype.ext ha⟩
  let j : Eˣ →* Aˣ := Units.map E.val.toRingHom.toMonoidHom
  have hj : Function.Injective j := Units.map_injective (f := E.val.toRingHom.toMonoidHom)
    E.val.injective
  have hAct (s : I) (u : Eˣ) : j ((q (s:G)) • u)=(s:G) • j u := by
    apply Units.ext
    change (j ((q (s:G)) • u) : A) = (((s:G) • j u) : A)
    simp only [j,Units.coe_map,AlgEquiv.smul_units_def,MonoidHom.coe_ofClass] <;> rfl
  have hPre (s : I) : ∃ u : Eˣ, j u=c s := by
    let x : E := ⟨(c s:A),hL s⟩
    have hx : x≠0 := fun h => (Units.ne_zero (c s)) (congrArg (fun a : E => (a:A)) h)
    refine ⟨Units.mk0 x hx,?_⟩
    apply Units.ext
    rfl
  let f (t : J) : Eˣ := Classical.choose (hPre (Classical.choose (hjr t)))
  have hVal (s : I) : j (f (jr s))=c s := by
    let l : I := Classical.choose (hjr (jr s))
    have he : q (l:G)=q (s:G) := congrArg (fun z : J => (z:Q)) (Classical.choose_spec (hjr (jr s)))
    exact (Classical.choose_spec (hPre l)).trans (hF l s he)
  have hf (x y : J) : f (x*y)=(x:Q) • f y*f x := by
    obtain ⟨s,rfl⟩ := hjr x
    obtain ⟨t,rfl⟩ := hjr y
    apply hj
    change j (f (jr s*jr t))=j ((q (s:G)) • f (jr t)*f (jr s))
    rw [← map_mul jr, hVal,map_mul,hAct,hVal,hVal]
    exact hc s t
  obtain ⟨a,ha⟩ := finite_subgroup_hilbert90 J f hf
  refine ⟨j a,fun s => ?_⟩
  have he := congrArg j (ha (jr s))
  change j ((q (s:G)) • a/a)=j (f (jr s)) at he
  rw [map_div,hAct,hVal] at he
  exact he

end CTActualClosedGaloisHilbert90318
