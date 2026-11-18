module
public import ActualPrimitiveMarkingClassCount318
public import PrimitiveDiamond318
public import Mathlib.LinearAlgebra.Dimension.Constructions
public section
noncomputable section
namespace ActualPrimitiveInvariantDegree318
open ActualPrimitiveMarkingClassCount318 PrimitiveTorsion318 EllipticTorsion318
open TensorProduct InvariantBaseChange318 EtaleInvariantQuotient318 OrbitAlgebra318
open scoped MatrixGroups

theorem orbits (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ) :
    Nat.card (Orbits H (PrimitiveDiamond318.Points N))≤(GammaHGroup318.gammaH N H).index := by
  classical
  let z := (Classical.choice (inferInstance : Nonempty UpperHalfPlane))
  let f (P:Points z N) : Orbits H (PrimitiveDiamond318.Points N) := ⟦(primitiveEquiv z N).symm P⟧
  have hf : Function.Surjective f := by
    intro q
    refine ⟨primitiveEquiv z N q.out,?_⟩
    simpa only [f,Equiv.symm_apply_apply] using q.out_eq
  apply (classes z N H f hf ?_).2
  intro u P Q hu
  apply Quotient.sound
  apply MulAction.orbitRel_apply.mpr
  refine ⟨u,?_⟩
  apply Subtype.ext
  apply torsionMap_injective z N
  have he (p:Points z N) : torsionMap z N ((primitiveEquiv z N).symm p).val=p.val :=
    congrArg Subtype.val ((primitiveEquiv z N).apply_symm_apply p)
  change torsionMap z N ((u.val • (primitiveEquiv z N).symm Q).val)=_
  rw [PrimitiveDiamond318.actual_point_scalar,he,he,hu]

/-- Purely algebraic alternative at the generic point, without identifying
any algebraic fibre with an analytic j-fibre. For the actual H-invariant
algebra of a primitive marking algebra that splits into the stated actual
coordinates after a field extension, the dimension is exactly the number
of H-orbits on primitive labels. There is no natural-number rank hypothesis
and no hypothesis that the scheme quotient has a prescribed degree. -/
theorem dimension (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    {k B S : Type*} [Field k] [CommRing B] [Algebra k B] [Field S] [Algebra k S]
    (ρ:H→B ≃ₐ[k] B)
    (e:S ⊗[k] B ≃ₐ[S] (PrimitiveDiamond318.Points N → S))
    (he:∀(g:H) (b:S ⊗[k] B) (x:PrimitiveDiamond318.Points N),
      e (baseAction S ρ g b) x=e b (g • x)) :
    Module.finrank k (invariants ρ)=Nat.card (Orbits H (PrimitiveDiamond318.Points N)) := by
  classical
  letI : Fintype (Orbits H (PrimitiveDiamond318.Points N)) := Fintype.ofFinite _
  let E := ((baseChangeEquiv S ρ).trans (splitInvariantEquiv (baseAction S ρ) e he)).trans
    (orbitEquiv S H (PrimitiveDiamond318.Points N)).symm
  rw [←Module.finrank_baseChange (R:=S) (M':=invariants ρ),E.toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card,Nat.card_eq_fintype_card]

/-- The field rank of the literal invariant algebra, usable before passing
to an algebraic closure, already has the modular-cover bound. -/
theorem degree (N:ℕ) [NeZero N] (H:Subgroup (ZMod N)ˣ)
    {k B S : Type*} [Field k] [CommRing B] [Algebra k B] [Field S] [Algebra k S]
    (ρ:H→B ≃ₐ[k] B) (e:S ⊗[k] B ≃ₐ[S] (PrimitiveDiamond318.Points N → S))
    (he:∀(g:H) (b:S ⊗[k] B) (x:PrimitiveDiamond318.Points N),
      e (baseAction S ρ g b) x=e b (g • x)) :
    (Module.finrank k (invariants ρ):ℝ)≤(N:ℝ)*H.index*EulerIndex318.eulerProduct N := by
  rw [dimension N H ρ e he]
  exact (Nat.cast_le.mpr (orbits N H)).trans (ActualGammaHIndexUpper318.gammaH_index N H)
end ActualPrimitiveInvariantDegree318
