module
public import FunctionFieldGluing318
public import AffineDominantTraceRestriction318
public import NormalAffineBasis318
public section
noncomputable section
namespace OpenDominantTraceExistence318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X Y:Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f:X⟶Y) [IsDominant f] [IsFinite f] (hY:NormalAffineBasis318.HasBasis Y)
    (hfinite:letI:=AffineDominantNorm318.fieldAlgebra f
      FiniteDimensional Y.functionField X.functionField)
include hY hfinite in
lemma exists_value (U:Y.Opens) [Nonempty U] (s:Γ(X,f⁻¹ᵁU)):
    letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
    letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
    ∃a:Γ(Y,U),Y.germToFunctionField U a=
      Algebra.trace Y.functionField X.functionField (X.germToFunctionField (f⁻¹ᵁU) s):=by
  letI:Nonempty (f⁻¹ᵁU):=DominantFunctionField318.preimage_nonempty f U
  letI:Algebra Y.functionField X.functionField:=AffineDominantNorm318.fieldAlgebra f
  choose V hle hx ha hn using hY U
  letI (x:U):Nonempty (V x):=⟨⟨x,hx x⟩⟩
  letI (x:U):IsIntegrallyClosed Γ(Y,V x):=hn x
  letI (x:U):Nonempty (f⁻¹ᵁV x):=DominantFunctionField318.preimage_nonempty f (V x)
  let sx (x:U):Γ(X,f⁻¹ᵁV x):=
    X.presheaf.map (homOfLE (f.preimage_mono (hle x))).op s
  let n (x:U):Γ(Y,V x):=AffineDominantTrace318.trace f (V x) (ha x) hfinite (sx x)
  have cover:U ≤ iSup V:=by
    intro x hxU
    exact Opens.mem_iSup.mpr ⟨⟨x,hxU⟩,hx ⟨x,hxU⟩⟩
  apply FunctionFieldGluing318.exists_section Y V U (fun x=>homOfLE (hle x)) cover n
  intro x
  rw [show n x=AffineDominantTrace318.trace f (V x) (ha x) hfinite (sx x) from rfl,
    AffineDominantTrace318.embedding]
  congr 1
  exact AffineDominantNormRestriction318.germ_restrict X _ s
end OpenDominantTraceExistence318
