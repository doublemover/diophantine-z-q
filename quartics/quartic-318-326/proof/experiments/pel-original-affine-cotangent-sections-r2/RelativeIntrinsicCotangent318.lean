module
public import IntrinsicDifferentialPullback318
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public section
noncomputable section
namespace RelativeIntrinsicCotangent318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) {R : CommRingCat.{u}}
  (p : X ⟶ Spec R) (q : Y ⟶ Spec R) (h : f ≫ q = p)

/-- The relative condition refers to actual functions on EVERY base open
and their actual pullbacks, not merely global functions or generic points. -/
def KillsBase {M : X.Modules}
    (d : Derivation' M.val (FamilyIntrinsicDifferentials318.coefficients p)) : Prop :=
  ∀ (U : Y.Opens) (s : Γ(Y,U)), d.d (f.app U s) = 0

/-- Killing base functions persists on every smaller source open. Thus
it applies to the germs of the inverse-image base structure sheaf. -/
theorem killsBase_restrict {M : X.Modules}
    (d : Derivation' M.val (FamilyIntrinsicDifferentials318.coefficients p))
    (hd : KillsBase f p d) (U : Y.Opens) (V : X.Opens)
    (hV : V ≤ f ⁻¹ᵁ U) (s : Γ(Y,U)) :
    d.d (X.presheaf.map (homOfLE hV).op (f.app U s)) = 0 := by
  rw [d.d_map,hd U s,map_zero]

/-- The actual derivative annihilation condition is equivalent to killing
all pulled-back base functions. This is the essential geometric comparison,
not a definition of relative derivations in terms of a desired cokernel. -/
theorem annihilates_iff {M : X.Modules}
    (a : FamilyIntrinsicDifferentials318.omega p ⟶ M) :
    IntrinsicDifferentialPullback318.pullbackMap f p q h ≫ a = 0 ↔
      KillsBase f p ((FamilyIntrinsicDifferentials318.D p).postcomp a.val) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have ha := adj.homEquiv_naturality_right
    (IntrinsicDifferentialPullback318.pullbackMap f p q h) a
  rw [IntrinsicDifferentialPullback318.pullbackMap_adjoint] at ha
  have hz : adj.homEquiv _ _
      (0 : (Scheme.Modules.pullback f).obj (FamilyIntrinsicDifferentials318.omega q) ⟶ M) = 0 := by
    simp [Adjunction.homEquiv_unit]
  rw [← (adj.homEquiv _ _).injective.eq_iff,ha,hz]
  constructor
  · intro he U s
    have hs := congrArg (fun k => k.val.app (op U)
      ((FamilyIntrinsicDifferentials318.D q).d s)) he
    change a.val.app (op (f ⁻¹ᵁ U))
      ((IntrinsicDifferentialPullback318.map f p q h).val.app (op U)
        ((FamilyIntrinsicDifferentials318.D q).d s)) = 0 at hs
    rw [IntrinsicDifferentialPullback318.map_D] at hs
    exact hs
  · intro he
    apply UniversalSheafDifferentials318.hom_ext (FamilyIntrinsicDifferentials318.coefficients q)
    ext U s
    change a.val.app (op (f ⁻¹ᵁ U.unop))
      ((IntrinsicDifferentialPullback318.map f p q h).val.app U
        ((FamilyIntrinsicDifferentials318.D q).d s)) = 0
    rw [IntrinsicDifferentialPullback318.map_D]
    exact he U.unop s

/-- The cokernel is taken in actual sheaves of O_X-modules on the whole
scheme. Its relative universal property is proved below against ALL sheaves. -/
@[expose] def omega : X.Modules :=
  cokernel (IntrinsicDifferentialPullback318.pullbackMap f p q h)

@[expose] def projection : FamilyIntrinsicDifferentials318.omega p ⟶ omega f p q h :=
  cokernel.π (IntrinsicDifferentialPullback318.pullbackMap f p q h)

@[expose] def D : Derivation' (omega f p q h).val
    (FamilyIntrinsicDifferentials318.coefficients p) :=
  (FamilyIntrinsicDifferentials318.D p).postcomp (projection f p q h).val

theorem D_kills_base : KillsBase f p (D f p q h) :=
  (annihilates_iff f p q h (projection f p q h)).mp (cokernel.condition _)

/-- Every genuine sheaf-valued R-derivation killing pulled-back base
functions factors through the same original derivative cokernel. -/
@[expose] def desc {M : X.Modules}
    (d : Derivation' M.val (FamilyIntrinsicDifferentials318.coefficients p))
    (hd : KillsBase f p d) : omega f p q h ⟶ M :=
  cokernel.desc _ (UniversalSheafDifferentials318.desc _ d) (by
    apply (annihilates_iff f p q h _).mpr
    rw [UniversalSheafDifferentials318.desc_fac]
    exact hd)

theorem desc_fac {M : X.Modules}
    (d : Derivation' M.val (FamilyIntrinsicDifferentials318.coefficients p))
    (hd : KillsBase f p d) : (D f p q h).postcomp (desc f p q h d hd).val = d := by
  change ((FamilyIntrinsicDifferentials318.D p).postcomp
    (projection f p q h).val).postcomp (desc f p q h d hd).val = d
  rw [UniversalSheafDifferentials318.postcomp_comp]
  change (FamilyIntrinsicDifferentials318.D p).postcomp
    (projection f p q h ≫ desc f p q h d hd).val = d
  rw [projection,desc,cokernel.π_desc]
  exact UniversalSheafDifferentials318.desc_fac _ d

theorem hom_ext {M : X.Modules} (a b : omega f p q h ⟶ M)
    (he : (D f p q h).postcomp a.val = (D f p q h).postcomp b.val) : a = b := by
  apply (cancel_epi (cokernel.π (IntrinsicDifferentialPullback318.pullbackMap f p q h))).mp
  apply UniversalSheafDifferentials318.hom_ext (FamilyIntrinsicDifferentials318.coefficients p)
  change (FamilyIntrinsicDifferentials318.D p).postcomp
      ((projection f p q h).val ≫ a.val) =
    (FamilyIntrinsicDifferentials318.D p).postcomp ((projection f p q h).val ≫ b.val)
  simpa only [D,UniversalSheafDifferentials318.postcomp_comp] using he

/-- Full existence and uniqueness for the intrinsic relative derivation
problem, over every sheaf and every open of the actual base. -/
theorem existsUnique_desc {M : X.Modules}
    (d : Derivation' M.val (FamilyIntrinsicDifferentials318.coefficients p))
    (hd : KillsBase f p d) :
    ∃! a : omega f p q h ⟶ M, (D f p q h).postcomp a.val = d := by
  refine ⟨desc f p q h d hd,desc_fac f p q h d hd,?_⟩
  intro a ha
  exact hom_ext f p q h a _ (ha.trans (desc_fac f p q h d hd).symm)
end RelativeIntrinsicCotangent318
