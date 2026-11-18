module
public import AllGenericMarkingFields318
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public section
noncomputable section
namespace CoarseOrbitResidueEmbedding318
open GenericMarkingOrbitField318 TranscendentalJGenericFiber318
open WeierstrassCurve.Affine
variable (N:ℕ) [NeZero N]
variable (L:Type*) [Field L] [Algebra (K N) L] [FiniteDimensional (K N) L] [IsGalois (K N) L]
variable (P:A N L) (hP:addOrderOf P=N) (H:Subgroup (ZMod N)ˣ)

private def coord : A N L → Bool→L
  | .zero, _ => 0
  | .some x _ _, true => x
  | .some _ y _, false => y

/-- Arbitrary rational coordinate observable with coefficients in the actual
generic base. For interpretation as a rational function at a point the
chosen denominator must not vanish at that point. -/
def eval (p q:MvPolynomial Bool (K N)) (Q:A N L) : L :=
  MvPolynomial.aeval (coord N L Q) p / MvPolynomial.aeval (coord N L Q) q

private theorem equivariant (g:G N L) (Q:A N L) (p q:MvPolynomial Bool (K N)) :
    g (eval N L p q Q)=eval N L p q (Point.map (W':=W N) g.toAlgHom Q) := by
  have hc (i:Bool) : g (coord N L Q i)=coord N L (Point.map (W':=W N) g.toAlgHom Q) i := by
    cases Q <;> cases i <;> simp [coord,Point.map_zero,Point.map_some]
  have ha : g.toAlgHom.comp (MvPolynomial.aeval (coord N L Q))=
      MvPolynomial.aeval (coord N L (Point.map (W':=W N) g.toAlgHom Q)) := by
    ext i
    simpa using hc i
  exact (map_div₀ g _ _).trans (congrArg₂ (· / ·) (DFunLike.congr_fun ha p) (DFunLike.congr_fun ha q))

variable {ι:Type*} (p q:ι→MvPolynomial Bool (K N))
abbrev residue := IntermediateField.adjoin (K N) (Set.range (fun i=>eval N L (p i) (q i) P))

/-- Any family of genuine rational values constant on the diamond orbit
generates a subfield of the orbit field. If the coarse quotient also
identifies negative markings or model automorphisms, the inclusion need
not be equality. -/
theorem residue_le
    (invariant : ∀(u:H) i, eval N L (p i) (q i) ((u.val:ZMod N).val • P) =
      eval N L (p i) (q i) P) :
    residue N L P p q≤orbitField N L P hP H := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i,rfl⟩
  intro g
  obtain ⟨u,hu⟩ := (mem_stabilizer N L P hP H g.val).mp g.property
  change g.val (eval N L (p i) (q i) P)=eval N L (p i) (q i) P
  rw [equivariant,hu,invariant]

/-- Enough for any actual coarse component whose function field embeds in
these invariant rational values. No identification of X_H with the fine
orbit field and no surjection from all labels is required. -/
theorem field_degree {F:Type*} [Field F] [Algebra (K N) F]
    (iota:F→ₐ[K N] residue N L P p q)
    (invariant : ∀(u:H) i, eval N L (p i) (q i) ((u.val:ZMod N).val • P) =
      eval N L (p i) (q i) P) :
    Module.finrank (K N) F≤(GammaHGroup318.gammaH N H).index := by
  let f := (IntermediateField.inclusion (residue_le N L P hP H p q invariant)).comp iota
  exact (LinearMap.finrank_le_finrank_of_injective (f:=f.toLinearMap) f.injective).trans
    (degree N L P hP H)
end CoarseOrbitResidueEmbedding318
