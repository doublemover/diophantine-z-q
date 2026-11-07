module
public import GammaOneAtlas318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318
open Filter Topology
namespace LocalDeck318
set_option maxHeartbeats 0

@[simp] theorem quotient_smul (N:ℕ) (g:image N) (z:UpperHalfPlane) :
    quotientMap N (g•z)=quotientMap N z := by
  apply Quotient.sound
  exact MulAction.orbitRel_apply.mpr ⟨g,rfl⟩

/-- Two genuine continuous lifts of the same quotient map differ locally by
one actual deck transformation. No local-constancy premise is supplied. -/
theorem locally_deck_eq {X:Type*} [TopologicalSpace X]
    (N:ℕ) (hN:5≤N) (f g:X→UpperHalfPlane) (x:X)
    (hf:ContinuousAt f x) (hg:ContinuousAt g x)
    (he:∀ᶠy in 𝓝 x,quotientMap N (f y)=quotientMap N (g y)) :
    ∃gamma:image N,(fun y=>gamma•f y)=ᶠ[𝓝 x]g := by
  have he0:=he.self_of_nhds
  obtain ⟨gamma,hgamma⟩:=MulAction.orbitRel_apply.mp (Quotient.exact he0.symm)
  let hloc:=quotient_localHomeomorph N hN
  let U: Set UpperHalfPlane := (hloc.localInverseAt (g x)).target
  have hU:U∈𝓝 (g x) :=
    (hloc.localInverseAt (g x)).open_target.mem_nhds hloc.self_mem_localInverseAt_target
  have hgU:∀ᶠy in 𝓝 x,g y∈U := hg.eventually hU
  have hcf:ContinuousAt (fun y=>gamma•f y) x :=
    (continuous_const_smul gamma).continuousAt.comp hf
  have hfU:∀ᶠy in 𝓝 x,gamma•f y∈U := hcf.eventually (by rw [hgamma]; exact hU)
  refine ⟨gamma,?_⟩
  filter_upwards [hfU,hgU,he] with y hyf hyg hye
  apply hloc.injOn_localInverseAt_target hyf hyg
  rw [quotient_smul,hye]
end LocalDeck318
