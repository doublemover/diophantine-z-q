module
public import ActualPrimitiveInvariantDegree318
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public section
noncomputable section
namespace CanonicalGeometricMarkingEvaluation318
open scoped TensorProduct
open InvariantBaseChange318 OrbitAlgebra318
variable {N : ℕ} [NeZero N] (H : Subgroup (ZMod N)ˣ)
variable {k B : Type*} [Field k] [CommRing B] [Algebra k B]
variable [Module.Finite k B] [Algebra.Etale k B]
variable (S : Type*) [Field S] [IsSepClosed S] [Algebra k S]
abbrev C (k S B:Type*) [Field k] [Field S] [Algebra k S] [CommRing B] [Algebra k B] := S ⊗[k] B
variable (ρ : H→B ≃ₐ[k] B)
variable (point : PrimitiveDiamond318.Points N→PrimeSpectrum (C k S B))
variable (equivariant : ∀ (g:H) x, point (g • x) =
  (point x).comap (baseAction S ρ g).toAlgHom)

private abbrev E := Algebra.FormallyEtale.equivPiOfIsSepClosed S (C k S B)

/-- Canonical evaluation on base-changed geometric points, not a chosen
algebra splitting. Invariance makes the values functions on genuine H-orbits. -/
def evaluate : invariants (baseAction S ρ) →ₐ[S]
    (Orbits H (PrimitiveDiamond318.Points N)→ S) where
  toFun b := Quotient.lift (fun x => E S (k:=k) (B:=B) b.val (point x)) (by
    intro x y h
    obtain ⟨g,hg⟩ := MulAction.orbitRel_apply.mp h
    rw [←hg,equivariant,Algebra.FormallyEtale.equivPiOfIsSepClosed_comap,
      b.property g])
  map_one' := by funext q;induction q using Quotient.inductionOn with | h x => exact congrFun (map_one (E S (k:=k) (B:=B))) _
  map_zero' := by funext q;induction q using Quotient.inductionOn with | h x => exact congrFun (map_zero (E S (k:=k) (B:=B))) _
  map_mul' b d := by funext q;induction q using Quotient.inductionOn with | h x => exact congrFun (map_mul (E S (k:=k) (B:=B)) b.val d.val) _
  map_add' b d := by funext q;induction q using Quotient.inductionOn with | h x => exact congrFun (map_add (E S (k:=k) (B:=B)) b.val d.val) _
  commutes' a := by funext q;induction q using Quotient.inductionOn with | h x => exact congrFun ((E S (k:=k) (B:=B)).commutes a) _

theorem injective (onto:Function.Surjective point) :
    Function.Injective (evaluate H S ρ point equivariant) := by
  intro b d h
  apply Subtype.ext
  apply (E S (k:=k) (B:=B)).injective
  funext q
  obtain ⟨x,rfl⟩ := onto q
  exact congrFun h (⟦x⟧ : Orbits H (PrimitiveDiamond318.Points N))

/-- For a finite étale fine marking algebra over the actual generic field,
surjectivity from primitive geometric markings and the diamond-compatibility
of this point map suffice. There is neither a prescribed equivariant
algebra splitting nor an injectivity requirement on geometric labels. -/
theorem rank (onto:Function.Surjective point) :
    Module.finrank k (invariants ρ)≤(GammaHGroup318.gammaH N H).index := by
  classical
  letI : Fintype (Orbits H (PrimitiveDiamond318.Points N)) := Fintype.ofFinite _
  let T := (evaluate H S ρ point equivariant).comp (baseChangeEquiv S ρ).toAlgHom
  have hi : Function.Injective T := (injective H S ρ point equivariant onto).comp (baseChangeEquiv S ρ).injective
  have hl := LinearMap.finrank_le_finrank_of_injective (f:=T.toLinearMap) hi
  rw [Module.finrank_baseChange,Module.finrank_fintype_fun_eq_card,←Nat.card_eq_fintype_card] at hl
  exact hl.trans (ActualPrimitiveInvariantDegree318.orbits N H)
end CanonicalGeometricMarkingEvaluation318
