module
public import Mathlib.Topology.Homotopy.Lifting
public section
noncomputable section
namespace SimplyConnectedCoverSheets318
open Set
universe u v w
variable {E:Type u} {X:Type v} {A:Type w}
  [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace A]
  [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
  (p:E→X) (S:Set X) (cov:IsCoveringMapOn p S)
  (f:C(A,X)) (hs:∀a,f a∈S) (a₀:A)

abbrev Fiber (a:A):={e:E // p e=f a}

/-- The global sheet through each point of the COMPLETE original base fiber.
Existence is actual simply-connected covering lifting, not cardinal choice. -/
@[expose] def sheet (e:Fiber p f a₀) : C(A,E):=
  (cov.existsUnique_continuousMap_lifts f e.property hs).exists.choose
lemma sheet_base (e:Fiber p f a₀) : sheet p S cov f hs a₀ e a₀=e.val :=
  (cov.existsUnique_continuousMap_lifts f e.property hs).exists.choose_spec.1
lemma sheet_lifts (e:Fiber p f a₀) : p ∘ sheet p S cov f hs a₀ e=f :=
  (cov.existsUnique_continuousMap_lifts f e.property hs).exists.choose_spec.2
lemma sheet_unique (e:Fiber p f a₀) (F:C(A,E)) (hF:F a₀=e.val) (hproj:p ∘ F=f) :
    F=sheet p S cov f hs a₀ e :=
  (cov.existsUnique_continuousMap_lifts f e.property hs).unique
    ⟨hF,hproj⟩ ⟨sheet_base p S cov f hs a₀ e,sheet_lifts p S cov f hs a₀ e⟩

/-- Distinct globally lifted sheets never meet anywhere in the base. -/
theorem sheet_injective_at (a:A) :
    Function.Injective (fun e:Fiber p f a₀=>sheet p S cov f hs a₀ e a) := by
  intro e d he
  have hl:p (sheet p S cov f hs a₀ e a)=f a := congrFun (sheet_lifts p S cov f hs a₀ e) a
  have hu:=cov.existsUnique_continuousMap_lifts f hl hs
  have heq:sheet p S cov f hs a₀ e=sheet p S cov f hs a₀ d := hu.unique
    ⟨rfl,sheet_lifts p S cov f hs a₀ e⟩ ⟨he.symm,sheet_lifts p S cov f hs a₀ d⟩
  apply Subtype.ext
  simpa only [sheet_base] using congrArg (fun F:C(A,E)=>F a₀) heq

/-- Every point of every full fiber occurs on one of these global sheets.
The total covering space need not be path-connected. -/
theorem sheet_exhaustive (a:A) (x:E) (hx:p x=f a) :
    ∃e:Fiber p f a₀,sheet p S cov f hs a₀ e a=x := by
  obtain ⟨F,⟨ha,hF⟩,_⟩:=cov.existsUnique_continuousMap_lifts f hx hs
  let e:Fiber p f a₀:=⟨F a₀,congrFun hF a₀⟩
  have he:F=sheet p S cov f hs a₀ e:=sheet_unique p S cov f hs a₀ e F rfl hF
  exact ⟨e,by rw [←he];exact ha⟩

/-- The same continuously constructed sheets identify ALL fibers with the
single fixed base fiber. This is not an arbitrary pointwise enumeration. -/
@[expose] def fiberEquiv (a:A) : Fiber p f a₀≃Fiber p f a :=
  Equiv.ofBijective (fun e=>⟨sheet p S cov f hs a₀ e a,congrFun (sheet_lifts p S cov f hs a₀ e) a⟩)
    ⟨by intro e d h;exact sheet_injective_at p S cov f hs a₀ a (congrArg Subtype.val h),
      by intro x;obtain ⟨e,he⟩:=sheet_exhaustive p S cov f hs a₀ a x.val x.property
         exact ⟨e,Subtype.ext he⟩⟩
end SimplyConnectedCoverSheets318
