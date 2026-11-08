module
public import LiteralKernelPrimitiveOpen318
public import F3PairIndependence318
public section
noncomputable section
namespace LiteralIndependentPairOpen318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318 LiteralKernelAddition318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "K" => ThreeTorsionTriplingFiber318.fiber (OpenJAffineScheme318.A N)
  (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)
/-- Four genuine universal kernel points: P, Q, Q-P and Q+P. -/
@[expose] def combination : Fin 4→Points N (productBase N):=
  ![leftPoint N,rightPoint N,rightPoint N-leftPoint N,rightPoint N+leftPoint N]
@[expose] def combinationMap (i:Fin 4) : product N ⟶ K:=(combination N i).val
@[expose] def nonzeroOpen (i:Fin 4) : (product N).Opens:=
  combinationMap N i ⁻¹ᵁ LiteralKernelPrimitiveOpen318.primitiveOpen N
/-- The actual ordered-independent-pair open. The exclusions are fiberwise
zero loci of genuine group combinations, not global inequalities of maps. -/
@[expose] def independentOpen : (product N).Opens:=
  nonzeroOpen N 0 ⊓ (nonzeroOpen N 1 ⊓ (nonzeroOpen N 2 ⊓ nonzeroOpen N 3))
@[expose] def scheme : Scheme:=(independentOpen N).toScheme
@[expose] def inclusion : scheme N ⟶ product N:=(independentOpen N).ι
instance inclusion_open : IsOpenImmersion (inclusion N):=by dsimp only [inclusion];infer_instance
lemma mem_independentOpen (x:product N) : x∈independentOpen N ↔
    combinationMap N 0 x∈LiteralKernelPrimitiveOpen318.primitiveOpen N ∧
    combinationMap N 1 x∈LiteralKernelPrimitiveOpen318.primitiveOpen N ∧
    combinationMap N 2 x∈LiteralKernelPrimitiveOpen318.primitiveOpen N ∧
    combinationMap N 3 x∈LiteralKernelPrimitiveOpen318.primitiveOpen N:=Iff.rfl
lemma nonzeroOpen_closed (i:Fin 4) : IsClosed (nonzeroOpen N i:Set (product N)):=
  (LiteralKernelPrimitiveOpen318.primitiveOpen_closed N).preimage (combinationMap N i).continuous
lemma independentOpen_closed : IsClosed (independentOpen N:Set (product N)):=
  (nonzeroOpen_closed N 0).inter ((nonzeroOpen_closed N 1).inter
    ((nonzeroOpen_closed N 2).inter (nonzeroOpen_closed N 3)))

/-- Each excluded locus is the actual inverse image of the actual zero
section under one of the four genuine group-combination maps. -/
@[expose] def zeroLocus (i:Fin 4) : Set (product N):=
  combinationMap N i ⁻¹' Set.range (LiteralKernelZeroSection318.toKernel N)
lemma zeroLocus_eq_complement (i:Fin 4) : zeroLocus N i=(nonzeroOpen N i:Set (product N))ᶜ:=by
  ext x
  simp only [zeroLocus,Set.mem_preimage,Set.mem_compl_iff]
  change _ ↔ ¬combinationMap N i x∈LiteralKernelPrimitiveOpen318.primitiveOpen N
  rw [LiteralKernelPrimitiveOpen318.mem_primitiveOpen_iff,not_not]
lemma zeroLocus_closed (i:Fin 4) : IsClosed (zeroLocus N i):=by
  rw [zeroLocus_eq_complement]
  exact (nonzeroOpen N i).isOpen.isClosed_compl
instance inclusion_closed : IsClosedImmersion (inclusion N):=by
  apply IsClosedImmersion.of_isPreimmersion
  change IsClosed (Set.range ((independentOpen N).ι))
  rw [Scheme.Opens.range_ι]
  exact independentOpen_closed N

variable {X:Scheme} (f:X ⟶ product N) (x:X)
@[expose] def atPoint : Points N (productBase N) →ₗ[ZMod 3]
    Points N ((X.fromSpecResidueField x ≫ f) ≫ productBase N):=
  LiteralKernelFunctor318.precomposeLinear N (productBase N) (X.fromSpecResidueField x ≫ f)
lemma atPoint_zero_iff (p:Points N (productBase N)) : atPoint N f x p=0 ↔
    p.val (f x)∈Set.range (LiteralKernelZeroSection318.toKernel N):=by
  have h:=LiteralKernelPrimitiveOpen318.point_zero_iff N
    ((X.fromSpecResidueField x ≫ f) ≫ productBase N) (atPoint N f x p)
    (IsLocalRing.closedPoint (X.residueField x))
  simpa only [atPoint,LiteralKernelFunctor318.precomposeLinear_value,
    Scheme.Hom.comp_apply,Scheme.fromSpecResidueField_apply] using h
lemma combination_nonzero_iff (i:Fin 4) :
    combinationMap N i (f x)∈LiteralKernelPrimitiveOpen318.primitiveOpen N ↔
      atPoint N f x (combination N i)≠0:=by
  rw [LiteralKernelPrimitiveOpen318.mem_primitiveOpen_iff]
  exact (not_congr (atPoint_zero_iff N f x (combination N i))).symm
/-- Actual residue-field F3 independence is exactly membership in this
open. Field values are used only to detect these open zero loci. -/
theorem mem_iff_independent : f x∈independentOpen N ↔
    LinearIndependent (ZMod 3) ![atPoint N f x (leftPoint N),atPoint N f x (rightPoint N)]:=by
  rw [mem_independentOpen,F3PairIndependence318.combinations_iff]
  simp [combination_nonzero_iff,combination]

/-- Fiberwise independence checks every test point, including every
component of a disconnected or nonreduced Scheme. -/
@[expose] def FiberwiseIndependent : Prop:=∀x:X,
  LinearIndependent (ZMod 3) ![atPoint N f x (leftPoint N),atPoint N f x (rightPoint N)]
lemma range_iff : Set.range f ⊆ Set.range (inclusion N) ↔ FiberwiseIndependent N f:=by
  rw [show Set.range (inclusion N)=(independentOpen N:Set (product N)) from Scheme.Opens.range_ι _]
  constructor
  · intro h x
    exact (mem_iff_independent N f x).mp (h ⟨x,rfl⟩)
  · intro h
    rintro _ ⟨x,rfl⟩
    exact (mem_iff_independent N f x).mpr (h x)
/-- Universal factorization through the actual open for arbitrary Scheme
tests; no dimension-two, pairing, or full-level conclusion is inserted. -/
theorem universal (h:FiberwiseIndependent N f) : ∃!g:X ⟶ scheme N,g ≫ inclusion N=f:=by
  let g:=IsOpenImmersion.lift (inclusion N) f ((range_iff N f).mpr h)
  have hg:g ≫ inclusion N=f:=IsOpenImmersion.lift_fac _ _ _
  exact ⟨g,hg,fun g' hg'=>(cancel_mono (inclusion N)).mp (hg'.trans hg.symm)⟩
theorem exists_iff : (∃g:X ⟶ scheme N,g ≫ inclusion N=f) ↔ FiberwiseIndependent N f:=by
  constructor
  · rintro ⟨g,rfl⟩
    apply (range_iff N _).mp
    rintro _ ⟨x,rfl⟩
    exact ⟨g x,rfl⟩
  · exact fun h=>(universal N f h).exists
end LiteralIndependentPairOpen318
