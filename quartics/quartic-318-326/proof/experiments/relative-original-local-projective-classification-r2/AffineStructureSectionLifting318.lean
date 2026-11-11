module
public import AffinePrincipalLocalLifts318
public import AdditiveSheafSections318

public section
noncomputable section
namespace AffineStructureSectionLifting318
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AdditiveSheafSections318
set_option maxHeartbeats 900000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : CommRingCat.{0}} [IsDomain R]
@[expose,reducible] def O : ASheaf (X:=PrimeSpectrum.Top R) :=
  ⟨(Spec.structureSheaf R).obj ⋙ StructureAdditiveSheaf318.additiveForget,
    CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _ _ (Spec.structureSheaf R).property⟩

omit [IsDomain R] in
theorem O_eq_original : O (R:=R) = StructureAdditiveSheaf318.sheaf (Spec R) := rfl
variable {F G : ASheaf (X:=PrimeSpectrum.Top R)}

/-- Global section lifting for any additive-sheaf extension with the original affine
structure sheaf as kernel. The middle and quotient sheaves need not be quasi-coherent. -/
theorem surjective (m : O (R:=R) ⟶ F) (p : F ⟶ G) (hw : m ≫ p = 0)
    (hS : (ShortComplex.mk m p hw).ShortExact) :
    Function.Surjective (p.hom.app (op ⊤)) := by
  classical
  have hm : Mono m := hS.mono_f
  have hp : Epi p := hS.epi_g
  intro t
  let l := AffinePrincipalLocalLifts318.data p t
  let := l.finiteIndex
  let f := l.element
  let s := l.localSection
  let d (i j : l.Index) : Sec F (PrimeSpectrum.basicOpen (f i*f j)) :=
    res F (PrimeSpectrum.basicOpen_mul_le_left _ _) (s i) -
      res F (PrimeSpectrum.basicOpen_mul_le_right _ _) (s j)
  have hd (i j : l.Index) : p.hom.app _ (d i j) = 0 := by
    dsimp [d]
    rw [map_sub,← hom_res,← hom_res,l.image,l.image]
    change res G _ (res G le_top t) - res G _ (res G le_top t) = 0
    rw [res_res,res_res,sub_self]
  have hc (i j : l.Index) : ∃ c : ActualPrincipalSections318.Sections (f i*f j),
      m.hom.app _ c = d i j :=
    TopCat.Sheaf.sections_exact_of_left_exact hS.exact hm (d i j) (hd i j)
  choose c hc using hc
  have hcc : ActualPrincipalCocycle318.Cocycle f c := by
    unfold ActualPrincipalCocycle318.Cocycle
    intro i j k
    apply app_injective m (PrimeSpectrum.basicOpen ((f i*f j)*f k))
    rw [map_add]
    change m.hom.app _ (res (O (R:=R)) _ (c i j)) +
      m.hom.app _ (res (O (R:=R)) _ (c j k)) =
      m.hom.app _ (res (O (R:=R)) _ (c i k))
    rw [← hom_res,← hom_res,← hom_res,hc,hc,hc]
    dsimp [d]
    simp only [map_sub]
    change (res F _ (res F _ (s i)) - res F _ (res F _ (s j))) +
      (res F _ (res F _ (s j)) - res F _ (res F _ (s k))) =
      res F _ (res F _ (s i)) - res F _ (res F _ (s k))
    simp only [res_res]
    abel
  obtain ⟨b,hb⟩ := ActualPrincipalCocycle318.split f l.nonzero l.covers c hcc
  let corrected (i : l.Index) : Sec F (PrimeSpectrum.basicOpen (f i)) :=
    s i-m.hom.app _ (b i)
  have hcorrected (i j : l.Index) :
      res F (PrimeSpectrum.basicOpen_mul_le_left (f i) (f j)) (corrected i) =
        res F (PrimeSpectrum.basicOpen_mul_le_right (f i) (f j)) (corrected j) := by
    have hh := hc i j
    rw [hb,map_sub] at hh
    change m.hom.app _ (res (O (R:=R)) _ (b i)) -
      m.hom.app _ (res (O (R:=R)) _ (b j)) = d i j at hh
    rw [← hom_res,← hom_res] at hh
    dsimp [corrected,d] at *
    simp only [map_sub]
    apply sub_eq_sub_iff_add_eq_add.mpr
    simpa only [add_comm] using (sub_eq_sub_iff_add_eq_add.mp hh).symm
  have hcompat : TopCat.Presheaf.IsCompatible F.obj
      (fun i => PrimeSpectrum.basicOpen (f i)) corrected := by
    intro i j
    apply ConcreteCategory.injective_of_mono_of_preservesPullback
      (F.obj.map (eqToHom (PrimeSpectrum.basicOpen_mul (f i) (f j))).op)
    change F.obj.map _ (F.obj.map _ _) = F.obj.map _ (F.obj.map _ _)
    rw [← F.obj.map_comp_apply,← F.obj.map_comp_apply]
    exact hcorrected i j
  obtain ⟨a,ha,_⟩ := TopCat.Sheaf.existsUnique_gluing' F
    (fun i => PrimeSpectrum.basicOpen (f i)) ⊤
    (fun i => AffinePrincipalLocalLifts318.toTop (f i)) l.covers.symm.le corrected hcompat
  refine ⟨a,?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' G (fun i => PrimeSpectrum.basicOpen (f i)) ⊤
    (fun i => AffinePrincipalLocalLifts318.toTop (f i)) l.covers.symm.le
  intro i
  change res G _ (p.hom.app _ a) = _
  rw [hom_res]
  have hai : res F le_top a = corrected i := ha i
  rw [hai]
  have hz : p.hom.app _ (m.hom.app _ (b i)) = 0 := by
    exact congrArg (fun q : O (R:=R) ⟶ G => q.hom.app _ (b i)) hw
  dsimp [corrected]
  calc
    _ = p.hom.app _ (s i) - p.hom.app _ (m.hom.app _ (b i)) := map_sub _ _ _
    _ = p.hom.app _ (s i) - 0 := congrArg (fun q => p.hom.app _ (s i)-q) hz
    _ = _ := (sub_zero _).trans (l.image i)

end AffineStructureSectionLifting318
