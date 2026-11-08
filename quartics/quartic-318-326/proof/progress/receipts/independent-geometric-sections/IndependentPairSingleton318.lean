module
public import KernelPairSections318
public import LiteralIndependentPairFinite318
public import F3RankTwoBases318
public section
noncomputable section
namespace IndependentPairSingleton318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318 LiteralKernelAddition318 LiteralIndependentPairOpen318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N : ℕ) {X : Scheme} [Subsingleton X]
variable (b : X ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
/-- On a singleton test, each original combination is zero precisely at the actual zero section. -/
lemma combination_nonzero (s : KernelPairSections318.Sections N b) (x : X) (i : Fin 4) :
    combinationMap N i (s.val x) ∈ LiteralKernelPrimitiveOpen318.primitiveOpen N ↔
      KernelPairSections318.restrict N b s.val s.property (combination N i) ≠ 0 := by
  rw [LiteralKernelPrimitiveOpen318.mem_primitiveOpen_iff]
  have hz := LiteralKernelPrimitiveOpen318.point_zero_iff N b
    (KernelPairSections318.restrict N b s.val s.property (combination N i)) x
  rw [KernelPairSections318.restrict_val, Scheme.Hom.comp_apply] at hz
  exact (not_congr hz).symm
/-- This is only a singleton-test reduction; it is not a global-inequality test on arbitrary Schemes. -/
theorem mem_iff (s : KernelPairSections318.Sections N b) (x : X) :
    s.val x ∈ independentOpen N ↔
      LinearIndependent (ZMod 3) ![KernelPairSections318.left N b s,KernelPairSections318.right N b s] := by
  rw [mem_independentOpen,F3PairIndependence318.combinations_iff]
  simp [combination_nonzero,combination,KernelPairSections318.left,KernelPairSections318.right]

abbrev Sections := {g : X ⟶ scheme N // g ≫ LiteralIndependentPairFinite318.structureMap N = b}
/-- Restriction of the exact independent-pair open to one specified base map. -/
@[expose] def toProduct (s : Sections N b) : KernelPairSections318.Sections N b :=
  ⟨s.val ≫ LiteralIndependentPairOpen318.inclusion N,by simpa only [LiteralIndependentPairFinite318.structureMap,Category.assoc] using s.property⟩
lemma toProduct_independent (s : Sections N b) (x : X) :
    LinearIndependent (ZMod 3) ![KernelPairSections318.left N b (toProduct N b s),
      KernelPairSections318.right N b (toProduct N b s)] := by
  apply (mem_iff N b _ x).mp
  exact (show Set.range (LiteralIndependentPairOpen318.inclusion N) = (independentOpen N : Set (product N)) from
    Scheme.Opens.range_ι _).le ⟨s.val x,rfl⟩

/-- Actual open sections are exactly the actual independent pair of kernel points, with explicit inverse lift. -/
@[expose] def equivalence (x : X) : Sections N b ≃ F3RankTwoBases318.Pairs (Points N b) where
  toFun s := ⟨(KernelPairSections318.left N b (toProduct N b s),
    KernelPairSections318.right N b (toProduct N b s)),
    (F3PairIndependence318.pair_iff _ _).mp (toProduct_independent N b s x)⟩
  invFun p := by
    let s := (KernelPairSections318.equiv N b).symm p.val
    have h : Set.range s.val ⊆ Set.range (LiteralIndependentPairOpen318.inclusion N) := by
      rw [show Set.range (LiteralIndependentPairOpen318.inclusion N) = (independentOpen N : Set (product N)) from Scheme.Opens.range_ι _]
      rintro _ ⟨y,rfl⟩
      apply (mem_iff N b s y).mpr
      have he := (KernelPairSections318.equiv N b).apply_symm_apply p.val
      change (KernelPairSections318.left N b s,KernelPairSections318.right N b s)=p.val at he
      rw [show KernelPairSections318.left N b s=p.val.1 from congrArg Prod.fst he,
        show KernelPairSections318.right N b s=p.val.2 from congrArg Prod.snd he]
      exact (F3PairIndependence318.pair_iff _ _).mpr p.property
    let g := IsOpenImmersion.lift (LiteralIndependentPairOpen318.inclusion N) s.val h
    refine ⟨g,?_⟩
    rw [LiteralIndependentPairFinite318.structureMap,←Category.assoc,IsOpenImmersion.lift_fac]
    exact s.property
  left_inv s := by
    apply Subtype.ext
    apply (cancel_mono (LiteralIndependentPairOpen318.inclusion N)).mp
    rw [IsOpenImmersion.lift_fac]
    exact congrArg Subtype.val ((KernelPairSections318.equiv N b).symm_apply_apply (toProduct N b s))
  right_inv p := by
    apply Subtype.ext
    change (KernelPairSections318.equiv N b) _=p.val
    rw [←(KernelPairSections318.equiv N b).apply_symm_apply p.val]
    apply (KernelPairSections318.equiv N b).congr_arg
    apply Subtype.ext
    exact IsOpenImmersion.lift_fac _ _ _

@[simp] theorem first_value (x : X) (s : Sections N b) :
    ((equivalence N b x s).val.1).val = s.val ≫ LiteralIndependentPairFunctor318.first N := by
  change (KernelPairSections318.left N b (toProduct N b s)).val = _
  rw [KernelPairSections318.left_val]
  exact Category.assoc _ _ _
@[simp] theorem second_value (x : X) (s : Sections N b) :
    ((equivalence N b x s).val.2).val = s.val ≫ LiteralIndependentPairFunctor318.second N := by
  change (KernelPairSections318.right N b (toProduct N b s)).val = _
  rw [KernelPairSections318.right_val]
  exact Category.assoc _ _ _
end IndependentPairSingleton318
