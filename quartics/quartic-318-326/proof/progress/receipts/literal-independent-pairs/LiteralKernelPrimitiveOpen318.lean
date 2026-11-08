module
public import LiteralKernelFunctor318
public import LiteralKernelPointCover318
public import Mathlib.AlgebraicGeometry.ResidueField
public section
noncomputable section
namespace LiteralKernelPrimitiveOpen318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD
local notation "j" => ThreeTorsionTriplingFiber318.toFiber A B hD
local notation "e" => LiteralKernelZeroSection318.toKernel N
instance primitive_open : IsOpenImmersion j:=(LiteralKernelOpenClosed318.canonical_open_closed N).1
instance primitive_closed : IsClosedImmersion j:=(LiteralKernelOpenClosed318.canonical_open_closed N).2
instance zero_open : IsOpenImmersion e:=by
  rw [←LiteralFullKernel318.inr_iso_inv N]
  infer_instance
@[expose] def primitiveOpen : (K).Opens:=(j).opensRange
lemma mem_primitiveOpen_iff (x:K) : x∈primitiveOpen N ↔ x∉Set.range e:=by
  change x∈Set.range j ↔ x∉Set.range e
  constructor
  · exact fun hj he=>(Set.disjoint_left.mp (LiteralKernelPointCover318.disjoint N)) hj he
  · intro he
    exact (LiteralKernelPointCover318.covers N x).resolve_right he
lemma primitiveOpen_closed : IsClosed (primitiveOpen N:Set K):=(j).isClosedEmbedding.isClosed_range

/-- For a singleton Scheme test, the actual point is zero exactly when its
underlying point lies in the actual open zero section. -/
theorem point_zero_iff {X:Scheme} [Subsingleton X]
    (b:X ⟶ Spec (CommRingCat.of (OpenJModel318.Base N))) (p:Points N b) (x:X) :
    p=0 ↔ p.val x∈Set.range e:=by
  constructor
  · rintro rfl
    rw [LiteralKernelScalar318.zero_val]
    exact ⟨b x,rfl⟩
  · intro hx
    have hr:Set.range p.val ⊆ Set.range e:=by
      rintro _ ⟨y,rfl⟩
      simpa only [Subsingleton.elim y x] using hx
    let f:=IsOpenImmersion.lift e p.val hr
    have hf:f ≫ e=p.val:=IsOpenImmersion.lift_fac _ _ _
    have hb:f=b:=by
      have h:=congrArg (fun g=>g ≫ structureMap N) hf
      simpa only [Category.assoc,structureMap,LiteralKernelZeroSection318.toKernel_snd,Category.comp_id]
        using h.trans p.property
    apply Subtype.ext
    rw [LiteralKernelScalar318.zero_val]
    exact hf.symm.trans (congrArg (fun u=>u ≫ e) hb)

/-- Residue-field restriction detects zero of a kernel point at that point;
this is not a claim that field points detect arbitrary Scheme-map equality. -/
theorem residue_zero_iff {X:Scheme}
    (b:X ⟶ Spec (CommRingCat.of (OpenJModel318.Base N))) (p:Points N b) (x:X) :
    LiteralKernelFunctor318.precompose N b (X.fromSpecResidueField x) p=0 ↔
      p.val x∈Set.range e:=by
  have h:=point_zero_iff N (X.fromSpecResidueField x ≫ b)
    (LiteralKernelFunctor318.precompose N b (X.fromSpecResidueField x) p)
    (IsLocalRing.closedPoint (X.residueField x))
  simpa only [LiteralKernelFunctor318.precompose,Scheme.Hom.comp_apply,Scheme.fromSpecResidueField_apply] using h
end LiteralKernelPrimitiveOpen318
