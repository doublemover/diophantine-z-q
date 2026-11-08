module
public import LiteralIndependentGeometricBases318
public import EtaleSectionTrivialization318
public section
noncomputable section
namespace KernelUniversalFrame318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N : ℕ)
@[expose] def Frame : Scheme := LiteralIndependentPairOpen318.scheme N
@[expose] def frameBase : Frame N ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)) :=
  LiteralIndependentPairFinite318.structureMap N
@[expose] def Kernel : Scheme := ThreeTorsionTriplingFiber318.fiber
  (OpenJAffineScheme318.A N) (OpenJAffineScheme318.B N) (OpenJAffineScheme318.discriminant_unit N)
@[expose] def family : Scheme := pullback (structureMap N) (frameBase N)
@[expose] def projection : family N ⟶ Frame N := pullback.snd _ _
@[expose] def original : family N ⟶ Kernel N := pullback.fst _ _
instance projection_etale : Etale (projection N) := by
  haveI : Etale (structureMap N) := (LiteralKernelFiniteEtale318.finite_etale N).2
  dsimp only [projection]
  infer_instance
@[expose] def first : Points N (frameBase N) :=
  ⟨LiteralIndependentPairFunctor318.first N,rfl⟩
@[expose] def second : Points N (frameBase N) :=
  ⟨LiteralIndependentPairFunctor318.second N,by
    rw [←LiteralIndependentPairFunctor318.first_base]
    rfl⟩
/-- Coefficients are genuine F3-linear combinations of the actual universal two points. -/
@[expose] def combination (c : Fin 2 → ZMod 3) : Points N (frameBase N) :=
  c 0 • first N + c 1 • second N
@[expose] def sectionMap (c : Fin 2 → ZMod 3) : Frame N ⟶ family N :=
  pullback.lift (combination N c).val (𝟙 _) (by simp only [Category.id_comp];exact (combination N c).property)
@[reassoc] theorem section_projection (c : Fin 2 → ZMod 3) :
    sectionMap N c ≫ projection N = 𝟙 _ := pullback.lift_snd _ _ _
@[reassoc] theorem section_original (c : Fin 2 → ZMod 3) :
    sectionMap N c ≫ original N = (combination N c).val := pullback.lift_fst _ _ _

variable {T : Scheme} (u : T ⟶ Frame N)
variable (b : T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))
variable (hu : u ≫ frameBase N = b)
/-- Actual kernel pullback maps over u correspond to actual original kernel points over b. -/
@[expose] def pointEquiv : {t : T ⟶ family N // t ≫ projection N = u} ≃ Points N b where
  toFun t := ⟨t.val ≫ original N,by
    rw [original,Category.assoc,pullback.condition,←Category.assoc]
    exact (congrArg (fun v => v ≫ frameBase N) t.property).trans hu⟩
  invFun q := ⟨pullback.lift q.val u (q.property.trans hu.symm),pullback.lift_snd _ _ _⟩
  left_inv t := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · exact (pullback.lift_snd _ _ _).trans t.property.symm
  right_inv q := by apply Subtype.ext;exact pullback.lift_fst _ _ _

@[expose] def restrict : Points N (frameBase N) →ₗ[ZMod 3] Points N b := by
  subst b
  exact LiteralKernelFunctor318.precomposeLinear N (frameBase N) u
@[simp] theorem restrict_val (p : Points N (frameBase N)) :
    (restrict N u b hu p).val = u ≫ p.val := by subst b;rfl

@[expose] def sectionValue (c : Fin 2 → ZMod 3) :
    {t : T ⟶ family N // t ≫ projection N = u} :=
  ⟨u ≫ sectionMap N c,by rw [Category.assoc,section_projection,Category.comp_id]⟩
/-- Exact evaluation of the original section before any geometric cardinality argument. -/
theorem value_coordinates (c : Fin 2 → ZMod 3) :
    pointEquiv N u b hu (sectionValue N u c) = restrict N u b hu (combination N c) := by
  apply Subtype.ext
  change (u ≫ sectionMap N c) ≫ original N = _
  rw [Category.assoc,section_original,restrict_val]
end KernelUniversalFrame318
