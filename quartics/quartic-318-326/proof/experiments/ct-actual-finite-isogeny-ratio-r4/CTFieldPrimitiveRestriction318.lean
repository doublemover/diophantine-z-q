module
public import CTFieldPrimitiveBoundary318
public import CTOriginalClosureFieldEmbedding318
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public section
noncomputable section

namespace CTFieldPrimitiveRestriction318

open CategoryTheory groupCohomology
open ActualTwoDescentClosureFieldEmbedding318

variable {F L : Type} [Field F] [Field L] [CharZero F] [CharZero L]

abbrev Gal (K : Type) [Field K] := Field.absoluteGaloisGroup K
abbrev FieldUnitRep (K : Type) [Field K] : Rep ℤ (Gal K) :=
  Rep.ofAlgebraAutOnUnits K (AlgebraicClosure K)

/-- The very same closure embedding as for the actual elliptic restriction. -/
def closureUnitMap (f : F →+* L) : FieldUnitRep F →+ FieldUnitRep L where
  toFun u := Additive.ofMul (Units.map (closureMap f).toMonoidHom u.toMul)
  map_zero' := by
    change Additive.ofMul (Units.map (closureMap f).toMonoidHom 1) = Additive.ofMul 1
    rw [map_one]
  map_add' u v := by
    let a : Additive ((AlgebraicClosure F)ˣ) := u
    let b : Additive ((AlgebraicClosure F)ˣ) := v
    change Additive.ofMul (Units.map (closureMap f).toMonoidHom (a.toMul*b.toMul)) =
      Additive.ofMul (Units.map (closureMap f).toMonoidHom a.toMul *
        Units.map (closureMap f).toMonoidHom b.toMul)
    rw [map_mul]

theorem closureUnitMap_equivariant (f : F →+* L) (s : Gal L) (u : FieldUnitRep F) :
    closureUnitMap f ((FieldUnitRep F).ρ (Field.absoluteGaloisGroup.map f s) u) =
      (FieldUnitRep L).ρ s (closureUnitMap f u) := by
  let a : Additive ((AlgebraicClosure F)ˣ) := u
  let σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := Field.absoluteGaloisGroup.map f s
  let τ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure L := s
  let M := Units.map (closureMap f).toMonoidHom
  change Additive.ofMul (M (σ • a.toMul))=Additive.ofMul (τ • M a.toMul)
  apply congrArg Additive.ofMul
  apply Units.ext
  change closureMap f (σ (a.toMul:AlgebraicClosure F))=τ (closureMap f (a.toMul:AlgebraicClosure F))
  exact actual_closure_map_galois f s (a.toMul:AlgebraicClosure F)

def unitRestrictionRep (f : F →+* L) :
    Rep.res (Field.absoluteGaloisGroup.map f).toMonoidHom (FieldUnitRep F) ⟶ FieldUnitRep L :=
  Rep.ofHom ⟨(closureUnitMap f).toIntLinearMap, fun s =>
    LinearMap.ext fun u => closureUnitMap_equivariant f s u⟩

abbrev unitRestrictionComplex (f : F →+* L) :=
  cochainsMap (Field.absoluteGaloisGroup.map f).toMonoidHom (unitRestrictionRep f)

def restrictCochain (f : F →+* L) (k : ℕ) (c : (Fin k → Gal F) → FieldUnitRep F) :
    (Fin k → Gal L) → FieldUnitRep L :=
  (unitRestrictionComplex f).f k c

theorem restrictCochain_apply (f : F →+* L) (k : ℕ)
    (c : (Fin k → Gal F) → FieldUnitRep F) (s : Fin k → Gal L) :
    restrictCochain f k c s =
      closureUnitMap f (c (fun i => Field.absoluteGaloisGroup.map f (s i))) := by rfl

theorem restrict_locallyConstant (f : F →+* L) (k : ℕ)
    (c : (Fin k → Gal F) → FieldUnitRep F) (hc : IsLocallyConstant c) :
    IsLocallyConstant (restrictCochain f k c) := by
  have h : Continuous (fun (s : Fin k → Gal L) (i : Fin k) =>
      Field.absoluteGaloisGroup.map f (s i)) :=
    continuous_pi fun i => (Field.absoluteGaloisGroup.map f).continuous.comp (continuous_apply i)
  exact (hc.comp_continuous h).comp (closureUnitMap f)

theorem restrict_d (f : F →+* L) (k : ℕ) (c : (Fin k → Gal F) → FieldUnitRep F) :
    inhomogeneousCochains.d (FieldUnitRep L) k (restrictCochain f k c) =
      restrictCochain f (k + 1) (inhomogeneousCochains.d (FieldUnitRep F) k c) := by
  have h := (unitRestrictionComplex f).comm k (k + 1)
  rw [inhomogeneousCochains.d_def (FieldUnitRep L),
    inhomogeneousCochains.d_def (FieldUnitRep F)] at h
  exact congrArg (fun e => e c) h

/-- Restrict the same global primitive and correct the precise local raw cup.
No local invariant, local vanishing of this corrected class, or reciprocity
is assumed or asserted. `hRaw` is the local cup comparison for the supplied
actual higher pairing, not a second primitive-existence input. -/
theorem corrected_cycle_of_restricted_primitive (f : ℚ →+* L)
    (e : CTFieldPrimitiveBoundary318.continuousTwo)
    (eta : (Fin 3 → Gal ℚ) → FieldUnitRep ℚ)
    (hPrimitive : inhomogeneousCochains.d (FieldUnitRep ℚ) 2 e.val = eta)
    (raw : (Fin 2 → Gal L) → FieldUnitRep L) (hCont : IsLocallyConstant raw)
    (hRaw : inhomogeneousCochains.d (FieldUnitRep L) 2 raw = restrictCochain f 3 eta) :
    ∃ z : cocycles (FieldUnitRep L) 2,
      iCocycles (FieldUnitRep L) 2 z = raw - restrictCochain f 2 e.val ∧
      IsLocallyConstant (iCocycles (FieldUnitRep L) 2 z) := by
  have hCycle : inhomogeneousCochains.d (FieldUnitRep L) 2
      (raw - restrictCochain f 2 e.val) = 0 := by
    rw [map_sub, hRaw, restrict_d, hPrimitive, sub_self]
  let z := cocyclesMk (raw - restrictCochain f 2 e.val) hCycle
  have hz : iCocycles (FieldUnitRep L) 2 z = raw - restrictCochain f 2 e.val :=
    iCocycles_mk _ _
  refine ⟨z, hz, ?_⟩
  rw [hz]
  exact (hCont.prodMk (restrict_locallyConstant f 2 e.val e.property)).comp
    fun p => p.1 - p.2

end CTFieldPrimitiveRestriction318
