module
public import OriginalReciprocalMinimaRectangle318
public import OriginalCovolumeIndex318
public section
noncomputable section
namespace OriginalWholeEuclideanBasis318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalFullEuclideanLattice318 OriginalControlledIntegralBasis318 OriginalWholeBasisCoordinates318
set_option maxHeartbeats 4000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Integer coefficient map into the SAME standard Euclidean original
lattice used by the covolume theorem. -/
@[expose] def coordinateEmbedding (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    (Fin 3 → ℤ) →ₗ[ℤ] realModule p κ t where
  toFun c := ⟨embed (synthesis u v z (c 0,c 1,c 2)),
    synthesis u v z (c 0,c 1,c 2),(intoLattice p κ t u v z hb (c 0,c 1,c 2)).property,rfl⟩
  map_add' a b := by
    apply Subtype.ext
    change embed (synthesis u v z ((a+b) 0,(a+b) 1,(a+b) 2))=
      embed (synthesis u v z (a 0,a 1,a 2))+embed (synthesis u v z (b 0,b 1,b 2))
    rw [←embedHom.map_add,←(synthesis u v z).map_add]
    rfl
  map_smul' a c := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp [synthesis,embed,smul_add,smul_smul] <;> ring

lemma coordinateEmbedding_bijective (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    Function.Bijective (coordinateEmbedding p κ t u v z hb) := by
  constructor
  · intro a b he
    have hh := embed_injective (congrArg Subtype.val he)
    have hc := synthesis_injective u v z (by simpa using hb.1.2) hh
    ext i
    fin_cases i
    · exact congrArg Prod.fst hc
    · exact congrArg (fun c : Vector ℤ => c.2.1) hc
    · exact congrArg (fun c : Vector ℤ => c.2.2) hc
  · intro y
    obtain ⟨x,hx,hxy⟩ := y.property
    obtain ⟨a,b,c,hc⟩ := hb.2 x hx
    refine ⟨![a,b,c],?_⟩
    apply Subtype.ext
    change embed (a • u+b • v+c • z)=y.val
    rw [←hc]
    exact hxy

@[expose] def coordinateEquiv (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    (Fin 3 → ℤ) ≃ₗ[ℤ] realModule p κ t :=
  LinearEquiv.ofBijective (coordinateEmbedding p κ t u v z hb)
    (coordinateEmbedding_bijective p κ t u v z hb)

/-- A genuine Mathlib Z-basis of the entire original Euclidean lattice,
constructed from actual integer coordinates rather than chosen abstractly. -/
@[expose] def wholeBasis (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) :
    Basis (Fin 3) ℤ (realModule p κ t) :=
  Basis.ofEquivFun (coordinateEquiv p κ t u v z hb).symm

lemma wholeBasis_apply (p : ι → ℕ) (κ : ℤ) (t : ∀ i, Option (ZMod (p i)))
    (u v z : Vector ℤ) (hb : IntegralBasisTriple p κ t u v z) (i : Fin 3) :
    (wholeBasis p κ t u v z hb i : E)=embed (![u,v,z] i) := by
  rw [wholeBasis,Basis.coe_ofEquivFun]
  change embed (synthesis u v z ((Pi.single i 1) 0,(Pi.single i 1) 1,(Pi.single i 1) 2))=
    embed (![u,v,z] i)
  fin_cases i <;> simp [synthesis,Pi.single_apply]

end OriginalWholeEuclideanBasis318
