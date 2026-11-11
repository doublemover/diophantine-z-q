module
public import OriginalControlledIntegralBasis318
public section
noncomputable section
namespace OriginalWholeBasisCoordinates318
open scoped BigOperators RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalAttainedMinima318 OriginalControlledIntegralBasis318 OriginalSaturatedPlane318
set_option maxHeartbeats 3000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer coordinate map of the constructed whole basis. The carrier
is the original integer triple, not a rational enlargement. -/
@[expose] def synthesis (u v z : Vector ℤ) : Vector ℤ →+ Vector ℤ where
  toFun c := c.1 • u+c.2.1 • v+c.2.2 • z
  map_zero' := by simp
  map_add' a b := by simp only [Prod.fst_add,Prod.snd_add,add_zsmul]; abel

lemma synthesis_injective (u v z : Vector ℤ)
    (h : LinearIndependent ℝ ![embed u,embed v,embed z]) :
    Function.Injective (synthesis u v z) := by
  intro a b hab
  have he := congrArg embed hab
  change embed (a.1 • u+a.2.1 • v+a.2.2 • z)=
    embed (b.1 • u+b.2.1 • v+b.2.2 • z) at he
  simp only [embedHom.map_add,embed_zsmul] at he
  have hs : ∑ i : Fin 3, ![(a.1:ℝ),(a.2.1:ℝ),(a.2.2:ℝ)] i • ![embed u,embed v,embed z] i=
      ∑ i : Fin 3, ![(b.1:ℝ),(b.2.1:ℝ),(b.2.2:ℝ)] i • ![embed u,embed v,embed z] i := by
    simpa [Fin.sum_univ_succ,add_assoc] using he
  have hc := Fintype.linearIndependent_iffₛ.mp h _ _ hs
  apply Prod.ext
  · have hh := hc 0
    exact_mod_cast hh
  · apply Prod.ext
    · have hh := hc 1
      exact_mod_cast hh
    · have hh := hc 2
      exact_mod_cast hh

@[expose] def intoLattice (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    Vector ℤ →+ literalLattice p κ t where
  toFun c := ⟨synthesis u v z c,
    (literalLattice p κ t).add_mem
      ((literalLattice p κ t).add_mem
        ((literalLattice p κ t).zsmul_mem (hb.1.1 0) c.1)
        ((literalLattice p κ t).zsmul_mem (hb.1.1 1) c.2.1))
      ((literalLattice p κ t).zsmul_mem (hb.1.1 2) c.2.2)⟩
  map_zero' := by apply Subtype.ext; exact (synthesis u v z).map_zero
  map_add' a b := by apply Subtype.ext; exact (synthesis u v z).map_add a b

/-- The entire original subgroup, not an unspecified finite-index
sublattice, is additively equivalent to integer coefficient triples. -/
@[expose] def wholeEquiv (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    Vector ℤ ≃+ literalLattice p κ t :=
  AddEquiv.ofBijective (intoLattice p κ t u v z hb) ⟨by
    intro a b hab
    exact synthesis_injective u v z (by simpa using hb.1.2) (congrArg Subtype.val hab),by
    intro y
    obtain ⟨a,b,c,hy⟩ := hb.2 y y.property
    exact ⟨(a,b,c),Subtype.ext hy.symm⟩⟩

lemma wholeEquiv_apply (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) (c : Vector ℤ) :
    (wholeEquiv p κ t u v z hb c).val=synthesis u v z c := rfl

lemma wholeEquiv_inverse (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z)
    (y : literalLattice p κ t) :
    synthesis u v z ((wholeEquiv p κ t u v z hb).symm y)=y.val :=
  congrArg Subtype.val ((wholeEquiv p κ t u v z hb).apply_symm_apply y)

/-- Same-point weighted sums can be transported without multiplicity loss:
the coefficient map is injective on every actual integer subset. -/
theorem synthesis_image_sum (u v z : Vector ℤ)
    (h : LinearIndependent ℝ ![embed u,embed v,embed z])
    (s : Finset (Vector ℤ)) (f : Vector ℤ → ℝ) :
    ∑ y ∈ s.image (synthesis u v z), f y = ∑ c ∈ s, f (synthesis u v z c) := by
  classical
  exact Finset.sum_image (fun a _ b _ hab => synthesis_injective u v z h hab)

end OriginalWholeBasisCoordinates318
