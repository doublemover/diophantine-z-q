module
public import NonreducedAffineLocalLifts318
public import AdditiveSheafSections318
public section
noncomputable section
namespace NonreducedAffineSectionLifting318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite AdditiveSheafSections318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{0}} [hX : IsAffine X]
local notation "O" => StructureAdditiveSheaf318.sheaf X
variable {F G : ASheaf (X:=X)}

include hX in
/-- Global sections lift in every additive-sheaf extension whose kernel is
the ORIGINAL structure sheaf of an arbitrary affine scheme. Neither the
middle nor the quotient sheaf is assumed quasi-coherent. -/
theorem surjective (m : O ⟶ F) (p : F ⟶ G) (hw : m ≫ p = 0)
    (hS : (ShortComplex.mk m p hw).ShortExact) :
    Function.Surjective (p.hom.app (op ⊤)) := by
  classical
  have hm : Mono m := hS.mono_f
  have hp : Epi p := hS.epi_g
  intro t
  let l := NonreducedAffineLocalLifts318.data p t
  let := l.finiteIndex
  let f := l.element
  let s := l.localSection
  let U := fun i => X.basicOpen (f i)
  let d (i j : l.Index) : Sec F (U i ⊓ U j) := res F inf_le_left (s i) - res F inf_le_right (s j)
  have hd (i j : l.Index) : p.hom.app _ (d i j) = 0 := by
    dsimp only [d]
    rw [map_sub,← hom_res,← hom_res,l.image,l.image]
    change res G _ (res G le_top t) - res G _ (res G le_top t) = 0
    rw [res_res,res_res,sub_self]
  have hc (i j : l.Index) : ∃ c : Γ(X,U i ⊓ U j), m.hom.app _ c = d i j :=
    TopCat.Sheaf.sections_exact_of_left_exact hS.exact hm (d i j) (hd i j)
  choose c hc using hc
  have hcc : OriginalPrincipalCocycleRows318.Cocycle X f c := by
    intro i j k
    apply app_injective m (U i ⊓ (U j ⊓ U k))
    rw [map_add]
    change m.hom.app _ (res O _ (c i j)) + m.hom.app _ (res O _ (c j k)) =
      m.hom.app _ (res O _ (c i k))
    rw [← hom_res,← hom_res,← hom_res,hc,hc,hc]
    dsimp only [d]
    simp only [map_sub,res_res]
    abel
  obtain ⟨b,hb⟩ := OriginalNonreducedCocycleSplit318.split_of_cover X f l.covers c hcc
  let corrected (i : l.Index) : Sec F (U i) := s i - m.hom.app _ (b i)
  have hcorrected (i j : l.Index) :
      res F inf_le_left (corrected i) = res F inf_le_right (corrected j) := by
    have hh := hc i j
    rw [hb,map_sub] at hh
    change m.hom.app _ (res O inf_le_left (b i)) -
      m.hom.app _ (res O inf_le_right (b j)) = d i j at hh
    rw [← hom_res,← hom_res] at hh
    dsimp only [corrected,d] at *
    simp only [map_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp hh).symm
  have hcompat : TopCat.Presheaf.IsCompatible F.obj U corrected := hcorrected
  obtain ⟨a,ha,_⟩ := TopCat.Sheaf.existsUnique_gluing' F U ⊤
    (fun i => homOfLE le_top) l.covers.symm.le corrected hcompat
  refine ⟨a,?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' G U ⊤ (fun i => homOfLE le_top) l.covers.symm.le
  intro i
  change res G _ (p.hom.app _ a) = _
  rw [hom_res]
  have hai : res F le_top a = corrected i := ha i
  rw [hai]
  have hz : p.hom.app _ (m.hom.app _ (b i)) = 0 :=
    congrArg (fun q : O ⟶ G => q.hom.app _ (b i)) hw
  dsimp only [corrected]
  calc
    _ = p.hom.app _ (s i) - p.hom.app _ (m.hom.app _ (b i)) := map_sub _ _ _
    _ = p.hom.app _ (s i) - 0 := congrArg (fun q => p.hom.app _ (s i)-q) hz
    _ = _ := (sub_zero _).trans (l.image i)
end NonreducedAffineSectionLifting318
