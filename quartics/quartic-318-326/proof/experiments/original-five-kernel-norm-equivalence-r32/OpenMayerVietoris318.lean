module
public import TerminalLocalCohomology318
public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris

public section
noncomputable section
namespace OpenMayerVietoris318
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}}

@[expose] def square (U V : Opens X) : Square (Opens X) where
  X₁ := U ⊓ V
  X₂ := U
  X₃ := V
  X₄ := ⊤
  f₁₂ := homOfLE inf_le_left
  f₁₃ := homOfLE inf_le_right
  f₂₄ := homOfLE le_top
  f₃₄ := homOfLE le_top
  fac := Subsingleton.elim _ _

theorem square_isPullback (U V : Opens X) : (square U V).IsPullback := by
  apply Square.IsPullback.mk
  refine PullbackCone.IsLimit.mk _
    (fun s => homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd))) ?_ ?_ ?_
  all_goals intros; apply Subsingleton.elim

theorem square_cover (U V : Opens X) (h : U ⊔ V = ⊤) :
    Sieve.ofTwoArrows (square U V).f₂₄ (square U V).f₃₄ ∈ Opens.grothendieckTopology X ⊤ := by
  intro x hx
  have hx' : x ∈ U ⊔ V := by rw [h]; exact hx
  rcases hx' with hxU | hxV
  · exact ⟨U,homOfLE le_top,⟨U,𝟙 _,homOfLE le_top,Presieve.ofArrows.mk WalkingPair.left,rfl⟩,hxU⟩
  · exact ⟨V,homOfLE le_top,⟨V,𝟙 _,homOfLE le_top,Presieve.ofArrows.mk WalkingPair.right,rfl⟩,hxV⟩

/-- The actual site square of two opens covering the full space. -/
@[expose] def mayerVietoris (U V : Opens X) (h : U ⊔ V = ⊤) :
    (Opens.grothendieckTopology X).MayerVietorisSquare :=
  .mk_of_isPullback (square U V) (square_isPullback U V) (square_cover U V h)

/-- The original Mayer–Vietoris boundary, with target the original global cohomology. -/
@[expose] def boundary (F : LocalSheafCohomologySections318.ASheaf (X:=X))
    (U V : Opens X) (h : U ⊔ V = ⊤) : F.H' 0 (U ⊓ V) →+ Sheaf.H F 1 :=
  (TerminalLocalCohomology318.equivalence X F 1).toAddMonoidHom.comp
    ((mayerVietoris U V h).δ F 0 1 rfl).hom

theorem boundary_surjective (F : LocalSheafCohomologySections318.ASheaf (X:=X))
    (U V : Opens X) (h : U ⊔ V = ⊤)
    (hU : ∀ x : F.H' 1 U, x = 0) (hV : ∀ x : F.H' 1 V, x = 0) :
    Function.Surjective (boundary F U V h) := by
  intro y
  let S := mayerVietoris U V h
  have hU' : ∀ x : F.H' 1 S.X₂, x = 0 := hU
  have hV' : ∀ x : F.H' 1 S.X₃, x = 0 := hV
  let x : F.H' 1 S.X₄ := (TerminalLocalCohomology318.equivalence X F 1).symm y
  have hx : (Ext.mk₀ S.shortComplex.g).comp x (zero_add 1) = 0 := by
    apply Ext.biprodAddEquiv.injective
    rw [map_zero]
    exact Prod.ext (hU' _) (hV' _)
  obtain ⟨z,hz⟩ := Ext.contravariant_sequence_exact₃ S.shortComplex_shortExact F x hx (n₀:=0) rfl
  refine ⟨z,?_⟩
  change (TerminalLocalCohomology318.equivalence X F 1)
    (S.shortComplex_shortExact.extClass.comp z (by decide)) = y
  rw [hz]
  exact (TerminalLocalCohomology318.equivalence X F 1).apply_symm_apply y
end OpenMayerVietoris318
