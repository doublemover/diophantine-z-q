module
public import AffineDerivationDetermination318
public section
noncomputable section
namespace DerivationFromBasis318
open AlgebraicGeometry CategoryTheory Opposite
open PresheafOfModulesOfCommRing
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {S : CommRingCat.{u}} {C : (Spec S).Opensᵒᵖ ⥤ CommRingCat.{u}}
    {φ : C ⟶ (Spec S).presheaf} {M : (Spec S).Modules}

local instance modulePresheaf (U : (Spec S).Opensᵒᵖ) :
    Module ((Spec S).presheaf.obj U) (M.presheaf.obj U) := (M.val.obj U).isModule

/-- Pointwise naturality of an additive presheaf map into an actual O-module sheaf. -/
theorem naturality_apply
    (α : (Spec S).presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶ M.presheaf)
    {U V : (Spec S).Opensᵒᵖ} (i : U ⟶ V) (a : (Spec S).presheaf.obj U) :
    (α.app V) ((Spec S).presheaf.map i a) = M.val.map i (α.app U a) :=
  congrArg (fun k => k a) (α.naturality i)

/-- An additive sheaf map is a derivation if the Leibniz and coefficient laws
hold on the actual affine basic-open basis. Sheaf separation proves the laws on
all opens, so no global Leibniz or coefficient premise is assumed. -/
@[expose] def fromBasis
    (α : (Spec S).presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶ M.presheaf)
    (hmul : ∀ (s : S) (a b : Γ(Spec S,PrimeSpectrum.basicOpen s)),
      α.app (op (PrimeSpectrum.basicOpen s)) (a*b) =
        a • α.app (op (PrimeSpectrum.basicOpen s)) b +
          b • α.app (op (PrimeSpectrum.basicOpen s)) a)
    (hbase : ∀ (s : S) (a : C.obj (op (PrimeSpectrum.basicOpen s))),
      α.app (op (PrimeSpectrum.basicOpen s)) (φ.app _ a)=0) :
    PresheafOfModulesOfCommRing.Derivation' M.val φ where
  d := (α.app _).hom
  d_map i a := naturality_apply α i a
  d_mul {X} a b := by
    change Γ(Spec S,X.unop) at a b
    apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
    intro x hx
    obtain ⟨_,⟨_,⟨s,rfl⟩,rfl⟩,hxs,hsU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx X.unop.2
    refine ⟨PrimeSpectrum.basicOpen s,hsU,hxs,?_⟩
    let V := PrimeSpectrum.basicOpen s
    let i := (homOfLE hsU).op
    let q : Γ(Spec S,X.unop) →+* Γ(Spec S,V) := ((Spec S).presheaf.map i).hom
    let r : Γ(M,X.unop) →+ Γ(M,V) := (M.val.map i).hom.toAddMonoidHom
    let du : Γ(Spec S,X.unop) →+ Γ(M,X.unop) := (α.app X).hom
    let dv : Γ(Spec S,V) →+ Γ(M,V) := (α.app (op V)).hom
    have hn (z : Γ(Spec S,X.unop)) : dv (q z)=r (du z) := naturality_apply α i z
    have hs (z : Γ(Spec S,X.unop)) (m : Γ(M,X.unop)) : r (z • m)=q z • r m :=
      M.val.map_smul i z m
    change r (du (a*b)) = r (a • du b + b • du a)
    calc
      r (du (a*b)) = dv (q (a*b)) := (hn _).symm
      _ = dv (q a * q b) := congrArg dv (q.map_mul a b)
      _ = q a • dv (q b) + q b • dv (q a) := hmul s _ _
      _ = q a • r (du b) + q b • r (du a) :=
        congrArg₂ (fun z w : Γ(M,V) => q a • z + q b • w) (hn b) (hn a)
      _ = r (a • du b) + r (b • du a) :=
        congrArg₂ HAdd.hAdd (hs a (du b)).symm (hs b (du a)).symm
      _ = r (a • du b + b • du a) := (r.map_add _ _).symm

  d_app {X} a := by
    apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
    intro x hx
    obtain ⟨_,⟨_,⟨s,rfl⟩,rfl⟩,hxs,hsU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx X.unop.2
    refine ⟨PrimeSpectrum.basicOpen s,hsU,hxs,?_⟩
    change M.val.map (homOfLE hsU).op (α.app X (φ.app X a)) =
      M.val.map (homOfLE hsU).op 0
    let i := (homOfLE hsU).op
    have h := congrArg (fun k => k a) (φ.naturality i)
    change φ.app _ (C.map i a) = (Spec S).presheaf.map i (φ.app X a) at h
    exact (naturality_apply α i (φ.app X a)).symm.trans
      ((congrArg (α.app _) h.symm).trans ((hbase s _).trans (map_zero _).symm))

end DerivationFromBasis318
