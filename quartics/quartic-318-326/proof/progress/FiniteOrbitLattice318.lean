module
public import IntegralLatticeDescent318
public section
namespace IntegralLatticeDescent318
set_option maxHeartbeats 0
noncomputable section
variable {H:Type*} [AddCommGroup H] [Module ℤ H]
variable {n:Type*} [Fintype n] [DecidableEq n]

/-- Finitely many finite basis-vector orbits force the actual integral
linear representation to have finite image. -/
theorem finite_image_of_basis_orbits {G:Type*} [Group G]
    (b:Module.Basis n ℤ H) (rho:G→*(H≃ₗ[ℤ]H))
    (horbit:∀i:n,(Set.range (fun g:G=>rho g (b i))).Finite) :
    (Set.range rho).Finite := by
  let C:n→Type _:=fun i=>Set.range (fun g:G=>rho g (b i))
  haveI (i:n):Finite (C i):=horbit i
  let ev:Set.range rho→∀i:n,C i:=fun e i=>
    ⟨e.val (b i),by obtain ⟨g,hg⟩:=e.property; exact ⟨g,congrArg (fun h:H≃ₗ[ℤ]H=>h (b i)) hg⟩⟩
  have he:Function.Injective ev := by
    intro e f hef
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply b.ext
    intro i
    exact congrArg Subtype.val (congrFun hef i)
  exact Finite.of_injective ev he

/-- A finite-rank free integral lattice with finite vector orbits and
trivial mod3 action has trivial actual action. -/
theorem finite_orbit_action_trivial [Module.Free ℤ H] [Module.Finite ℤ H]
    {G:Type*} [Group G] (rho:G→*(H≃ₗ[ℤ]H))
    (horbit:∀x:H,(Set.range (fun g:G=>rho g x)).Finite)
    (hmod:∀g x,∃y:H,rho g x-x=(3:ℤ) • y) : ∀g x,rho g x=x := by
  apply finite_image_action_trivial rho
  · exact finite_image_of_basis_orbits (Module.Free.chooseBasis ℤ H) rho (fun i=>horbit _)
  · exact hmod

end
end IntegralLatticeDescent318
#print axioms IntegralLatticeDescent318.finite_orbit_action_trivial
