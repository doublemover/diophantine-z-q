module
public import GenericPrimitiveFiberBound318
public import OrbitValueFixedField318
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public section
noncomputable section
namespace GenericMarkingOrbitField318
open TranscendentalJGenericFiber318 GenericPrimitiveFiberBound318
open PrimitiveDiamond318 OpenJAnalyticPoints318 OrbitAlgebra318
open WeierstrassCurve.Affine
variable (N:ℕ) [NeZero N]
local instance : Algebra (K N) ℂ := (embedding N τ h ht).toAlgebra
abbrev W := ((OpenJModel318.integralModel N).map (algebraMap _ (K N))).toAffine
abbrev A (L:Type*) [Field L] [Algebra (K N) L] := ((W N).baseChange L).Point

private def castPoint {U V : WeierstrassCurve.Affine ℂ} (q:U=V) : U.Point ≃+ V.Point := by
  subst V
  exact AddEquiv.refl _
private def comparison : A N ℂ ≃+ (OpenJComplexEvaluation318.fiber N τ h).toAffine.Point :=
  castPoint (congrArg WeierstrassCurve.toAffine (actual_curve N τ h ht))

variable (L:Type*) [Field L] [Algebra (K N) L] [FiniteDimensional (K N) L] [IsGalois (K N) L]
abbrev G := L ≃ₐ[K N] L
private def conjugate (g:G N L) : A N L →+ A N L := Point.map (W':=W N) g.toAlgHom
private theorem conjugate_mul (g j:G N L) (P:A N L) :
    conjugate N L (g*j) P=conjugate N L g (conjugate N L j P) := by
  cases P <;> rfl
private theorem conjugate_one (P:A N L) : conjugate N L 1 P=P := by cases P <;> rfl
private def toFiber : A N L →+ (OpenJComplexEvaluation318.fiber N τ h).toAffine.Point :=
  (comparison N).toAddMonoidHom.comp (Point.map (W':=W N) (IsAlgClosed.lift:L→ₐ[K N]ℂ))
private theorem toFiber_inj : Function.Injective (toFiber N L) :=
  (comparison N).injective.comp (Point.map_injective (W':=W N) _)

variable (P:A N L) (hP:addOrderOf P=N)

private def label (g:G N L) : Points N :=
  (primitiveEquiv N τ h N).symm ⟨toFiber N L (conjugate N L g P), by
    rw [addOrderOf_injective (toFiber N L) (toFiber_inj N L),
        addOrderOf_injective (conjugate N L g) (Point.map_injective (W':=W N) _),hP]⟩
private theorem label_spec (g:G N L) :
    torsionMap N τ h N (label N L P hP g).val=toFiber N L (conjugate N L g P) :=
  congrArg Subtype.val ((primitiveEquiv N τ h N).apply_symm_apply _)

variable (H:Subgroup (ZMod N)ˣ)
private def value (g:G N L) : Orbits H (Points N) := ⟦label N L P hP g⟧
private theorem value_eq (a b:G N L) :
    value N L P hP H a=value N L P hP H b ↔ ∃u:H,
      conjugate N L a P = (u.val:ZMod N).val • conjugate N L b P := by
  have scalar (u:H) (g:G N L) :
      torsionMap N τ h N (u • label N L P hP g).val =
        (u.val:ZMod N).val • toFiber N L (conjugate N L g P) := by
    change torsionMap N τ h N (PrimitiveDiamond318.scalar N u.val _) = _
    rw [scalar_eq_nsmul,map_nsmul,label_spec]
  constructor
  · intro hh
    obtain ⟨u,hu⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hh)
    refine ⟨u,toFiber_inj N L ?_⟩
    rw [map_nsmul,←scalar u b,hu,label_spec]
  · rintro ⟨u,hu⟩
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    refine ⟨u,Subtype.ext (torsionMap_injective N τ h N ?_)⟩
    rw [scalar,label_spec,hu,map_nsmul]

private theorem left_invariant (t a b:G N L)
    (hh:value N L P hP H a=value N L P hP H b) :
    value N L P hP H (t*a)=value N L P hP H (t*b) := by
  obtain ⟨u,hu⟩ := (value_eq N L P hP H a b).mp hh
  exact (value_eq N L P hP H _ _).mpr ⟨u,by rw [conjugate_mul,conjugate_mul,hu,map_nsmul]⟩

/-- Genuine arithmetic stabilizer of the H-orbit of the given point. -/
def stabilizer : Subgroup (G N L) :=
  OrbitValueFixedField318.stabilizer (value N L P hP H) (left_invariant N L P hP H)

theorem mem_stabilizer (g:G N L) :
    g∈stabilizer N L P hP H ↔ ∃u:H, Point.map (W':=W N) g.toAlgHom P=(u.val:ZMod N).val • P := by
  change value N L P hP H g=value N L P hP H 1 ↔ _
  simpa only [conjugate_one] using (value_eq N L P hP H g 1)

abbrev orbitField := IntermediateField.fixedField (stabilizer N L P hP H)

/-- Degree for a literal field of moduli of the marked H-orbit over the actual
generic arithmetic j-line, for every algebraic mark given in a finite Galois
extension. Neither an algebra splitting, a moduli-point surjection nor a
degree equality with a modular scheme is assumed. -/
theorem degree : Module.finrank (K N) (orbitField N L P hP H)≤(GammaHGroup318.gammaH N H).index := by
  rw [OrbitValueFixedField318.finrank_fixed]
  exact (OrbitValueFixedField318.index (value N L P hP H) (left_invariant N L P hP H)).trans
    (ActualPrimitiveInvariantDegree318.orbits N H)

end GenericMarkingOrbitField318
