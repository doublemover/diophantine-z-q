module
public import PrimitiveXEquationDegree318
public import GaloisFiniteRootPolynomial318
public section
noncomputable section
namespace CanonicalPrimitiveXPolynomial318
open TranscendentalJGenericFiber318 GenericPrimitiveFiberBound318
open GenericMarkingOrbitField318 GenericPrimitiveXCoordinate318 AllGenericMarkingFields318
open WeierstrassCurve.Affine
variable (N:ℕ) [NeZero N]
local instance : Algebra (K N) ℂ := (embedding N τ h ht).toAlgebra
variable (L:IntermediateField (K N) ℂ) [FiniteDimensional (K N) L] [IsGalois (K N) L]
abbrev Marks := {P:A N L // addOrderOf P=N}
private def inj : Marks N L → T N := fun Q=>⟨Point.map (W':=W N) L.val Q.val,
  (addOrderOf_injective _ (Point.map_injective (W':=W N) L.val) Q.val).trans Q.property⟩
instance : Finite (Marks N L) := by
  letI : Finite (T N) := Finite.of_equiv _ (periodLabels N)
  exact Finite.of_injective (inj N L) (fun _ _ h => Subtype.ext
    (Point.map_injective (W':=W N) L.val (congrArg Subtype.val h)))

def nodes : Finset L := (Set.finite_range (fun Q:Marks N L=>x N L Q.val)).toFinset
theorem mem_nodes (a:L) : a∈nodes N L ↔ ∃P:A N L,addOrderOf P=N ∧ x N L P=a := by
  classical
  rw [nodes,Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨⟨p,hP⟩,hh⟩;exact ⟨p,hP,hh⟩
  · rintro ⟨p,hP,hh⟩;exact ⟨⟨p,hP⟩,hh⟩
theorem stable (g:G N L) (a:L) (ha:a∈nodes N L) : g a∈nodes N L := by
  obtain ⟨P,hP,rfl⟩ := (mem_nodes N L a).mp ha
  refine (mem_nodes N L _).mpr ⟨Point.map (W':=W N) g.toAlgHom P,
    (addOrderOf_injective _ (Point.map_injective (W':=W N) g.toAlgHom) P).trans hP,?_⟩
  cases P <;> simp [x,Point.map_some,Point.map_zero]

def q : Polynomial (K N) := GaloisFiniteRootPolynomial318.poly (nodes N L) (stable N L)
theorem monic : (q N L).Monic := GaloisFiniteRootPolynomial318.monic _ _
theorem separable : (q N L).Separable := GaloisFiniteRootPolynomial318.separable _ _
theorem q_degree : (q N L).natDegree=(nodes N L).card := GaloisFiniteRootPolynomial318.degree _ _
theorem roots : ((q N L).map (algebraMap (K N) L)).roots=(nodes N L).val :=
  GaloisFiniteRootPolynomial318.roots _ _
theorem zero_iff (a:L) : Polynomial.aeval a (q N L)=0 ↔
    ∃P:A N L,addOrderOf P=N ∧ x N L P=a :=
  (GaloisFiniteRootPolynomial318.zero_iff _ _ _).trans (mem_nodes N L a)

/-- For N>1 and a simultaneous L chosen upstream these are precisely
all primitive geometric x-coordinates on the generic curve. Irreducibility,
not an assumed annihilation, a supplied polynomial or its guessed degree,
is the sole equation input left for the concrete diamond-field bound. -/
theorem bound_of_irreducible (P:A N L) (hP:addOrderOf P=N) (H:Subgroup (ZMod N)ˣ)
    (irr:Irreducible (q N L)) :
    let ann : ∀Q:A N L,addOrderOf Q=N → Polynomial.aeval (x N L Q) (q N L)=0 :=
      fun Q hQ=>(zero_iff N L _).mpr ⟨Q,hQ,rfl⟩
    (Module.finrank (K N) (invariantField N L P H
      (PrimitiveXEquationDegree318.common_minpoly N L P hP H (q N L) irr ann)):ℝ) ≤
        (N:ℝ)*H.index*EulerIndex318.eulerProduct N :=
  PrimitiveXEquationDegree318.degree N L P hP H (q N L) irr
    (fun Q hQ=>(zero_iff N L _).mpr ⟨Q,hQ,rfl⟩)
/-- On the simultaneous finite field the true COMPLEX roots are exactly all
geometric primitive x-values. The N>1 guard excludes the identity at infinity. -/
theorem exists_full_primitive_equation (_hN:1<N) :
    ∃p:Polynomial (K N), p.Monic ∧ p.Separable ∧ ∀z:ℂ,
      Polynomial.aeval z p=0 ↔ ∃Q:A N ℂ,addOrderOf Q=N ∧ x N ℂ Q=z := by
  classical
  obtain ⟨L,hd,hg,hall⟩ := AllGenericMarkingFields318.simultaneous N
  letI := hd
  letI := hg
  refine ⟨q N L,monic N L,separable N L,?_⟩
  intro z
  have fac : Polynomial.aeval z (q N L) = ∏a∈nodes N L,(z-(a:ℂ)) := by
    calc
      _ = Polynomial.aeval (R:=L) z ((q N L).map (algebraMap (K N) L)) := by
        simp [Polynomial.aeval_def,Polynomial.eval₂_map,←IsScalarTower.algebraMap_eq]
      _ = _ := by
        rw [q,GaloisFiniteRootPolynomial318.map_poly]
        simp
  rw [fac,Finset.prod_eq_zero_iff]
  have hcoord (R:A N L) : x N ℂ (Point.map (W':=W N) L.val R)=(x N L R:L) := by
    cases R <;> simp [x,Point.map_some,Point.map_zero]
  constructor
  · rintro ⟨a,ha,hz⟩
    obtain ⟨R,hR,rfl⟩ := (mem_nodes N L a).mp ha
    exact ⟨Point.map (W':=W N) L.val R,
      (addOrderOf_injective _ (Point.map_injective (W':=W N) L.val) R).trans hR,
      (hcoord R).trans (sub_eq_zero.mp hz).symm⟩
  · rintro ⟨Q,hQ,rfl⟩
    obtain ⟨v,hv⟩ := (periodLabels N).surjective (⟨Q,hQ⟩:T N)
    obtain ⟨R,hR,he,_⟩ := hall v
    have hi : Point.map (W':=W N) L.val R=Q := he.trans (congrArg Subtype.val hv)
    refine ⟨x N L R,(mem_nodes N L _).mpr ⟨R,hR,rfl⟩,?_⟩
    exact sub_eq_zero.mpr (hi ▸ hcoord R)
end CanonicalPrimitiveXPolynomial318
