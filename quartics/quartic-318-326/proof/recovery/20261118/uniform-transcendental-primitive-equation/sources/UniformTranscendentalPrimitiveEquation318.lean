module
public import CanonicalPrimitiveXPolynomial318
public section
noncomputable section
namespace UniformTranscendentalPrimitiveEquation318
open WeierstrassCurve.Affine TranscendentalJGenericFiber318
open GenericMarkingOrbitField318 PrimitiveDiamond318 CanonicalPrimitiveXPolynomial318
open OpenJComplexEvaluation318
variable (N:ℕ) [NeZero N]
local instance reference : Algebra (K N) ℂ :=
  (embedding N GenericPrimitiveFiberBound318.τ GenericPrimitiveFiberBound318.h
    GenericPrimitiveFiberBound318.ht).toAlgebra
abbrev ArithmeticMarks (τ:UpperHalfPlane) (h:Admissible τ) :=
  {P:(fiber N τ h).toAffine.Point // addOrderOf P=N}
private def castPoint {U V:WeierstrassCurve.Affine ℂ} (hh:U=V) : U.Point ≃+ V.Point := by
  subst V
  exact AddEquiv.refl _
def valueX {F:Type*} [Field F] {V:WeierstrassCurve.Affine F} : V.Point→F
  | .zero=>0 | .some a _ _=>a
private theorem cast_x {U V:WeierstrassCurve.Affine ℂ} (hh:U=V) (P:U.Point) :
    valueX (castPoint hh P)=valueX P := by subst V; rfl

/-- No selected numerical zero is analytically continued. For *each*
transcendental period, the arithmetic generic splitting field embeds over
that period's own j-value. The same finite polynomial therefore has exactly
the actual geometric x-values at every such period. -/
theorem uniform (_hN:1<N) : ∃Q:Polynomial (K N), Q.Monic ∧ Q.Separable ∧
    ∀(τ:UpperHalfPlane) (h:Admissible τ) (ht:Transcendental ℤ (ActualQJ318.jInvariant τ))
      (z:ℂ), Q.eval₂ (embedding N τ h ht) z=0 ↔
      ∃P:ArithmeticMarks N τ h,valueX P.val=z := by
  classical
  obtain ⟨L,hd,hg,hall⟩ := AllGenericMarkingFields318.simultaneous N
  letI := hd;letI := hg
  let M := Marks N L
  let v₀ (p:M) : AllGenericMarkingFields318.T N :=
    ⟨Point.map (W':=W N) L.val p.val,
      (addOrderOf_injective _ (Point.map_injective (W':=W N) L.val) p.val).trans p.property⟩
  have hi : Function.Injective v₀ := fun _ _ hh=>Subtype.ext
    (Point.map_injective (W':=W N) L.val (congrArg Subtype.val hh))
  have hsur : Function.Surjective v₀ := by
    intro Q
    obtain ⟨v,rfl⟩ := (AllGenericMarkingFields318.periodLabels N).surjective Q
    obtain ⟨p,hp,he,_⟩ := hall v
    exact ⟨⟨p,hp⟩,Subtype.ext he⟩
  let labels := (Equiv.ofBijective v₀ ⟨hi,hsur⟩).trans
    (AllGenericMarkingFields318.periodLabels N).symm
  refine ⟨q N L,monic N L,separable N L,?_⟩
  intro τ h ht z
  let e := embedding N τ h ht
  letI target : Algebra (K N) ℂ := e.toAlgebra
  let φ : L →ₐ[K N] ℂ := IsAlgClosed.lift
  have hcoeff (a:K N) : φ (algebraMap (K N) L a)=e a := φ.commutes a
  let eqW := congrArg WeierstrassCurve.toAffine (actual_curve N τ h ht)
  let v := (castPoint eqW).toAddMonoidHom.comp (Point.map (W':=W N) φ)
  have hv : Function.Injective v := (castPoint eqW).injective.comp (Point.map_injective (W':=W N) φ)
  have hcoord (p:A N L) : valueX (v p)=φ (x N L p) := by
    change valueX (castPoint eqW (Point.map (W':=W N) φ p))=_
    rw [cast_x]
    cases p <;> simp [valueX,x,Point.map_zero,Point.map_some]
  let w (p:M) : ArithmeticMarks N τ h :=
    ⟨v p.val,(addOrderOf_injective v hv p.val).trans p.property⟩
  have hw : Function.Injective w := fun _ _ hh=>Subtype.ext (hv (congrArg Subtype.val hh))
  letI : Fintype M := Fintype.ofFinite _
  let equiv := labels.trans (OpenJAnalyticPoints318.primitiveEquiv N τ h N)
  letI : Fintype (ArithmeticMarks N τ h) := Fintype.ofEquiv M equiv
  have full : Function.Surjective w :=
    ((Fintype.bijective_iff_injective_and_card w).mpr ⟨hw,Fintype.card_congr equiv⟩).2
  have fac : (q N L).eval₂ e z=∏a∈nodes N L,(z-φ a) := by
    have comp : φ.toRingHom.comp (algebraMap (K N) L)=e := RingHom.ext hcoeff
    calc
      _ = ((q N L).map (algebraMap (K N) L)).eval₂ φ.toRingHom z := by
        rw [Polynomial.eval₂_map,comp]
      _ = _ := by
        rw [q,GaloisFiniteRootPolynomial318.map_poly]
        simp
  rw [fac,Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨a,ha,hz⟩
    obtain ⟨p,hp,rfl⟩ := (mem_nodes N L _).mp ha
    exact ⟨w ⟨p,hp⟩,(hcoord p).trans (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨p,rfl⟩
    obtain ⟨t,rfl⟩ := full p
    exact ⟨x N L t.val,(mem_nodes N L _).mpr ⟨t.val,t.property,rfl⟩,
      sub_eq_zero.mpr (hcoord t.val)⟩
end UniformTranscendentalPrimitiveEquation318
