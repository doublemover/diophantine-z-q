module
public import LocalCohomologyRestriction318
public import OpenMayerVietoris318
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public section
noncomputable section
namespace MayerVietorisSectionKernel318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
open LocalSheafCohomologySections318 LocalSheafCohomologyAdditive318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}}

theorem delta_kernel (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (F : ASheaf (X:=X)) (x : F.H' 0 S.X₁) :
    S.δ F 0 1 rfl x = 0 ↔ ∃ (a : F.H' 0 S.X₂) (b : F.H' 0 S.X₃),
      (F.cohomologyPresheaf 0).map S.f₁₂.op a -
        (F.cohomologyPresheaf 0).map S.f₁₃.op b = x := by
  have hex := (S.sequence_exact F 0 1 rfl).exact 1
  change (ShortComplex.mk (S.fromBiprod F 0) (S.δ F 0 1 rfl) (S.fromBiprod_δ F 0 1 rfl)).Exact at hex
  rw [ShortComplex.ab_exact_iff] at hex
  constructor
  · intro hx
    obtain ⟨y,hy⟩ := hex x hx
    obtain ⟨⟨a,b⟩,rfl⟩ := (AddCommGrpCat.biprodIsoProd (F.H' 0 S.X₂) (F.H' 0 S.X₃)).addCommGroupIsoToAddEquiv.symm.surjective y
    exact ⟨a,b,(S.fromBiprod_biprodIsoProd_inv_apply F a b).symm.trans hy⟩
  · rintro ⟨a,b,hab⟩
    let y := (AddCommGrpCat.biprodIsoProd (F.H' 0 S.X₂) (F.H' 0 S.X₃)).inv (a,b)
    have hy : S.fromBiprod F 0 y = x := (S.fromBiprod_biprodIsoProd_inv_apply F a b).trans hab
    rw [← hy,← ConcreteCategory.comp_apply,S.fromBiprod_δ]
    rfl

@[expose] def sectionBoundary (F : ASheaf (X:=X)) (U V : Opens X) (h : U ⊔ V = ⊤) :
    F.obj.obj (op (U ⊓ V)) →+ Sheaf.H F 1 :=
  (OpenMayerVietoris318.boundary F U V h).comp (zeroAddEquiv F (U ⊓ V)).symm.toAddMonoidHom

theorem sectionBoundary_kernel (F : ASheaf (X:=X)) (U V : Opens X) (h : U ⊔ V = ⊤)
    (x : F.obj.obj (op (U ⊓ V))) :
    sectionBoundary F U V h x = 0 ↔ ∃ (a : F.obj.obj (op U)) (b : F.obj.obj (op V)),
      F.obj.map (homOfLE inf_le_left : U ⊓ V ⟶ U).op a -
        F.obj.map (homOfLE inf_le_right : U ⊓ V ⟶ V).op b = x := by
  let S := OpenMayerVietoris318.mayerVietoris U V h
  let z : F.H' 0 S.X₁ := (zeroAddEquiv F (U ⊓ V)).symm x
  have hb : sectionBoundary F U V h x = 0 ↔ S.δ F 0 1 rfl z = 0 := by
    change (TerminalLocalCohomology318.equivalence X F 1) (S.δ F 0 1 rfl z) = 0 ↔ _
    exact (TerminalLocalCohomology318.equivalence X F 1).map_eq_zero_iff
  rw [hb,delta_kernel]
  constructor
  · rintro ⟨a,b,hab⟩
    refine ⟨zeroAddEquiv F S.X₂ a,zeroAddEquiv F S.X₃ b,?_⟩
    have he := congrArg (zeroAddEquiv F S.X₁) hab
    rw [map_sub,LocalCohomologyRestriction318.zero_naturality F S.f₁₂,
      LocalCohomologyRestriction318.zero_naturality F S.f₁₃] at he
    simpa only [z,AddEquiv.apply_symm_apply] using he
  · rintro ⟨a,b,hab⟩
    refine ⟨(zeroAddEquiv F S.X₂).symm a,(zeroAddEquiv F S.X₃).symm b,?_⟩
    apply (zeroAddEquiv F S.X₁).injective
    rw [map_sub,LocalCohomologyRestriction318.zero_naturality F S.f₁₂,
      LocalCohomologyRestriction318.zero_naturality F S.f₁₃]
    simpa only [z,AddEquiv.apply_symm_apply] using hab
end MayerVietorisSectionKernel318
