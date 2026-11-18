module
public import FiniteConjugateOrbitAlgebraic318
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.Galois.GaloisClosure
public section
noncomputable section
namespace FiniteGeometricTorsionField318
open WeierstrassCurve.Affine Set
variable {k Ω:Type*} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] [CharZero k]
variable (W:WeierstrassCurve.Affine k) (N:ℕ)
abbrev Points := {P : (W.baseChange Ω).Point // addOrderOf P=N}
private def pair : (W.baseChange Ω).Point → Ω×Ω
  | .zero => (0,0)
  | .some x y _ => (x,y)
private def coord (j:Bool) (P:Points (Ω:=Ω) W N) : Ω :=
  if j then (pair W P.val).1 else (pair W P.val).2
private def act (σ:Ω ≃ₐ[k] Ω) (P:Points (Ω:=Ω) W N) : Points (Ω:=Ω) W N :=
  ⟨Point.map (W':=W) σ.toAlgHom P.val,
    (addOrderOf_injective _ (Point.map_injective (W':=W) σ.toAlgHom) _).trans P.property⟩
private theorem coord_act (j:Bool) (σ:Ω≃ₐ[k]Ω) (P:Points (Ω:=Ω) W N) :
    coord W N j (act W N σ P)=σ (coord W N j P) := by
  rcases P with ⟨p,h⟩
  cases p <;> cases j <;> simp [coord,pair,act,Point.map_zero,Point.map_some]

variable [Finite (Points (Ω:=Ω) W N)]
theorem coordinate_algebraic (j:Bool) (P:Points (Ω:=Ω) W N) :
    IsAlgebraic k (coord W N j P) := by
  apply FiniteConjugateOrbitAlgebraic318.algebraic_of_finite
  refine (Set.finite_range (coord W N j)).subset ?_
  rintro _ ⟨σ,rfl⟩
  exact ⟨act W N σ P,coord_act W N j σ P⟩

/-- All geometric marks simultaneously, in a single actual finite Galois
subextension of the ambient algebraically closed field, even if that
ambient field is not algebraic over the ground field. -/
theorem exists_field : ∃ L:IntermediateField k Ω,
    FiniteDimensional k L ∧ IsGalois k L ∧
    ∀ P:Points (Ω:=Ω) W N, ∃ Q:(W.baseChange L).Point,
      addOrderOf Q=N ∧ Point.map (W':=W) L.val Q=P.val := by
  classical
  let s := range (fun t:Bool × Points (Ω:=Ω) W N => coord W N t.1 t.2)
  have fs : s.Finite := Set.finite_range _
  letI := fs.fintype
  let E := IntermediateField.adjoin k s
  letI : FiniteDimensional k E := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨⟨j,P⟩,rfl⟩
    exact (coordinate_algebraic W N j P).isIntegral)
  let L := IntermediateField.normalClosure k E Ω
  letI : IsNormalClosure k E L :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (F:=k) (K:=E) (L:=Ω)
      (fun z=>IsAlgClosed.splits _)
  letI : Normal k L := IsNormalClosure.normal (K:=E)
  letI : IsGalois k L := { }
  refine ⟨L,inferInstance,inferInstance,?_⟩
  intro P
  have mem (j:Bool) : coord W N j P∈L :=
    IntermediateField.le_normalClosure E (IntermediateField.subset_adjoin k s ⟨(j,P),rfl⟩)
  obtain ⟨Q,hQ⟩ : ∃ Q:(W.baseChange L).Point, Point.map (W':=W) L.val Q=P.val := by
    rcases P with ⟨p,hp⟩
    cases p with
    | zero => exact ⟨0,rfl⟩
    | some x y hh =>
      let x' : L := ⟨x,mem true⟩
      let y' : L := ⟨y,mem false⟩
      exact ⟨Point.some x' y' ((W.baseChange_nonsingular L.val.injective x' y').mp hh),rfl⟩
  refine ⟨Q,?_,hQ⟩
  exact (addOrderOf_injective _ (Point.map_injective (W':=W) L.val) Q).symm.trans
    ((congrArg addOrderOf hQ).trans P.property)
end FiniteGeometricTorsionField318
