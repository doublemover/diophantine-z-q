module
public import AllGenericMarkingFields318
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public section
noncomputable section
namespace GenericPrimitiveXCoordinate318
open TranscendentalJGenericFiber318 GenericMarkingOrbitField318 WeierstrassCurve.Affine
open IntermediateField
variable (N:ℕ) [NeZero N]
variable (L:Type*) [Field L] [Algebra (K N) L] [FiniteDimensional (K N) L] [IsGalois (K N) L]
def x : A N L → L | .zero => 0 | .some a _ _ => a
private theorem x_neg (P:A N L) : x N L (-P)=x N L P := by
  cases P <;> rfl
private theorem x_map (g:G N L) (P:A N L) :
    g (x N L P)=x N L (Point.map (W':=W N) g.toAlgHom P) := by
  cases P <;> simp [x,Point.map_zero,Point.map_some]
abbrev F₁ (P:A N L) := IntermediateField.adjoin (K N) {x N L P}
abbrev gen (P:A N L) : F₁ N L P := AdjoinSimple.gen _ _
private theorem sign_of_fix (g:G N L) (P:A N L) (hx:g (x N L P)=x N L P) :
    Point.map (W':=W N) g.toAlgHom P=P ∨ Point.map (W':=W N) g.toAlgHom P= -P := by
  apply Point.eq_or_eq_neg_of_xRep_eq_xRep
  cases P with
  | zero => rfl
  | some a b hp =>
    change g a=a at hx
    simp only [Point.map_some,Point.xRep_some,hx]

/-- All scalar multiples have x in the SAME simple field, without knowing
division polynomial formulas or assuming the ambient extension is abelian.
At O the value 0 is only a total-function convention; the modular chart
uses the affine locus N>1, and N=1 has base field Q(j). -/
theorem multiple_mem (P:A N L) (m:ℕ) : x N L (m • P) ∈ F₁ N L P := by
  rw [←IsGalois.fixedField_fixingSubgroup (F₁ N L P)]
  intro g
  have hf : g.val (x N L P)=x N L P := g.property (gen N L P)
  change g.val (x N L (m • P))=x N L (m • P)
  rw [x_map,map_nsmul]
  rcases sign_of_fix N L g.val P hf with hh|hh
  · rw [hh]
  · rw [hh,nsmul_neg,x_neg]

variable (P:A N L) (H:Subgroup (ZMod N)ˣ)
abbrev XP (u:H) := x N L ((u.val:ZMod N).val • P)
variable (root_condition : ∀u:H, minpoly (K N) (x N L P)=minpoly (K N) (XP N L P H u))

/-- The actual x-coordinate diamond endomorphism, constructed from its
generator and primitive-root conjugacy, not an action given on all functions. -/
def diamond (u:H) : F₁ N L P →ₐ[K N] F₁ N L P :=
  (IntermediateField.inclusion (IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr (multiple_mem N L P _)))).comp
    (minpoly.algEquiv (Algebra.IsAlgebraic.isAlgebraic (x N L P)) (root_condition u)).toAlgHom

theorem diamond_gen (u:H) :
    ((diamond N L P H root_condition u (gen N L P): F₁ N L P):L)=XP N L P H u := by
  change ((minpoly.algEquiv _ (root_condition u) (AdjoinSimple.gen _ _) :
    IntermediateField.adjoin (K N) {XP N L P H u}):L)=_
  rw [minpoly.algEquiv_apply]
  rfl

def invariantField : IntermediateField (K N) (F₁ N L P) where
  carrier := {z | ∀u:H,diamond N L P H root_condition u z=z}
  zero_mem' := fun _=>map_zero _
  one_mem' := fun _=>map_one _
  add_mem' {p q} hp hq := fun u=>by rw [map_add,hp u,hq u]
  neg_mem' {p} hp := fun u=>by rw [map_neg,hp u]
  mul_mem' {p q} hp hq := fun u=>by rw [map_mul,hp u,hq u]
  inv_mem' {p} hp := fun u=>by rw [map_inv₀,hp u]
  algebraMap_mem' a := fun u=>(diamond N L P H root_condition u).commutes a

/-- The computed diamond fixed subfield maps into the Galois orbit-stabilizer
field. This is not equality in general, notably when -1 is not in H. -/
theorem bound (hP:addOrderOf P=N) :
    Module.finrank (K N) (invariantField N L P H root_condition)≤(GammaHGroup318.gammaH N H).index := by
  let F := F₁ N L P
  let D := invariantField N L P H root_condition
  let i := F.val.comp D.val
  have holds (z:D) : i z∈orbitField N L P hP H := by
    intro g
    obtain ⟨u,hu⟩ := (mem_stabilizer N L P hP H g.val).mp g.property
    have he : g.val.toAlgHom.comp F.val = F.val.comp (diamond N L P H root_condition u) := by
      apply IntermediateField.adjoin_algHom_ext
      rintro a (rfl : a=x N L P)
      change g.val (x N L P)=((diamond N L P H root_condition u (gen N L P):F):L)
      rw [diamond_gen,x_map,hu]
    change g.val (i z)=i z
    exact (DFunLike.congr_fun he z.val).trans (congrArg (fun v:F=>(v:L)) (z.property u))
  let f := i.codRestrict (orbitField N L P hP H).toSubalgebra holds
  exact (LinearMap.finrank_le_finrank_of_injective (f:=f.toLinearMap) f.injective).trans
    (degree N L P hP H)
end GenericPrimitiveXCoordinate318
