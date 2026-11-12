module
public import ActualDifferentialTriple318
public section
noncomputable section
namespace TripleOpen318
open AlgebraicGeometry CategoryTheory
open ActualDifferentialTriple318 DifferentialChartMaps318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

section Generic
variable {S T U : Type u} [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]
theorem spec_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U) :
    Spec.map (CommRingCat.ofHom (g.comp f).toRingHom)=
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  change Spec.map (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom g.toRingHom)=_
  exact Spec.map_comp _ _

theorem open_comp (f : S →ₐ[R] T) (g : T →ₐ[R] U)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))]
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom g.toRingHom))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (g.comp f).toRingHom)) := by
  rw [spec_comp]
  infer_instance
end Generic

theorem fromFI_open (A B : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=FI A B) (S:=Triple A B) (fromFI A B).toRingHom)) :=
  IsOpenImmersion.of_isLocalization (extraMinor A B)

theorem fromY_open (A B : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=FiniteChart A B) (S:=Triple A B) (fromY A B).toRingHom)) := by
  letI := fromFI_open A B
  letI := ActualInfinityOpen318.finite_open A B
  exact open_comp _ _

theorem fromInfinity_open (A B : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=InfinityChart A B) (S:=Triple A B) (fromInfinity A B).toRingHom)) := by
  letI := fromFI_open A B
  letI := ActualInfinityOpen318.infinity_open A B
  exact open_comp _ _

/-- The actual triple-to-finite-overlap map is open, by the exact source diamond. -/
theorem fromXY_open (A B : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=XY A B) (S:=Triple A B) (fromXY A B).toRingHom)) := by
  let f:=Spec.map (CommRingCat.ofHom (R:=XY A B) (S:=Triple A B) (fromXY A B).toRingHom)
  let g:=Spec.map (CommRingCat.ofHom (FiniteInvariantDifferential318.yMap A B).toRingHom)
  have hg : IsOpenImmersion g := FiniteOverlapSheaves318.y_open A B
  have hfg : IsOpenImmersion (f ≫ g) := by
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=XY A B) (S:=Triple A B) (fromXY A B).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (FiniteInvariantDifferential318.yMap A B).toRingHom))
    rw [←spec_comp,←y_diamond]
    exact fromY_open A B
  exact IsOpenImmersion.of_comp f g

theorem fromX_open (A B : R) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (R:=FiniteInvariantDifferential318.XChart A B) (S:=Triple A B) (fromX A B).toRingHom)) := by
  letI := fromXY_open A B
  letI := FiniteOverlapSheaves318.x_open A B
  exact open_comp _ _
end TripleOpen318
