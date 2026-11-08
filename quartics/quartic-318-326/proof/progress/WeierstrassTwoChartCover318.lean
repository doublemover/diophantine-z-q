module
public import WeierstrassGluing318
public import GenericProductCover318
public section
noncomputable section
namespace WeierstrassTwoChartCover318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {R:Type u} [CommRing R]
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def chart (A B:R) (i:Fin 2) : Scheme :=
  Fin.cases (ShortAffineScheme318.scheme A B) (fun _=>InfinitySmooth318.scheme A B) i
@[expose] def intoCurve (A B:R) (i:Fin 2) : chart A B i ⟶ WeierstrassGluing318.scheme A B := by
  refine Fin.cases ?_ (fun i=>Fin.cases ?_ (fun i=>Fin.elim0 i) i) i
  · exact WeierstrassGluing318.finiteChart A B
  · exact WeierstrassGluing318.infinityChart A B
instance intoCurve_open (A B:R) (i:Fin 2) : IsOpenImmersion (intoCurve A B i) := by
  fin_cases i
  · exact WeierstrassGluing318.finiteChart_open A B
  · exact WeierstrassGluing318.infinityChart_open A B
@[expose] def cover (A B:R) : (WeierstrassGluing318.scheme A B).OpenCover where
  I₀:=Fin 2
  X:=chart A B
  f:=intoCurve A B
  mem₀:=by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_,fun i=>intoCurve_open A B i⟩
    intro p
    rcases WeierstrassGluing318.charts_cover A B p with h|h
    · exact ⟨0,h⟩
    · exact ⟨1,h⟩
@[expose] def productCover (A B:R) :
    (pullback (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B)).OpenCover :=
  GenericProductCover318.cover (cover A B) (cover A B)
    (WeierstrassGluing318.structureMap A B) (WeierstrassGluing318.structureMap A B)
end WeierstrassTwoChartCover318
