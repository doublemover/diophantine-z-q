module
public import OrientedSourceLabels318
public section
namespace SourceLabelData318
open ConcreteG8Domain (K)
open CircuitReplay Raw318FinalReplay CompressedGeneratorBridge318
open LocalGenerator318 GlobalGeneratorPoints318 RawOddAnchorPoints318
set_option maxHeartbeats 0
noncomputable section

/-- A single coherent global witness, chosen independently of any contact
prime, ties both actual point families, the root labels, the scalar index,
and the common two-torsion offset together. -/
structure Labels (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) where
  uLabel : Fin 4→ℤ
  vLabel : Fin 4→ℤ
  c : ℤ
  n : ℤ
  tau : E.Point
  primary : ∀j,uLabel j • P=transport curve_eq (RawRootDifference318.U ((3:ℚ)^65536) w source j)
  alternate : ∀j,vLabel j • P=transport curve_eq (RawRootDifference318.V ((3:ℚ)^65536) w source j)
  roots : RootLabels w (fun j=>uLabel j-vLabel j)
  scalar : ScalarLabel w c
  odd : ∀j,Odd (uLabel j-vLabel j)
  orientation : c=(uLabel 1-vLabel 1)-1 ∨ c= -(uLabel 1-vLabel 1)-1
  anchor_divides : (2*3^32767:ℤ)∣c
  anchor_bound : (2:ℝ)^49151<(c.natAbs:ℝ)
  index_ne : n≠0
  torsion : tau=0 ∨ tau=T 0
  H : transport curve_eq (CompressedTranslation318.H ((3:ℚ)^65536) w source)=n • P+tau
  V : transport curve_eq (CompressedTranslation318.V ((3:ℚ)^65536) w source)=(n-1) • P+tau

theorem labels_exist (w:Assignment) (source:Constraints (stage0 ((3:ℚ)^65536)) w) :
    Nonempty (Labels w source) := by
  obtain ⟨u,v,c,n,t,hu,hv,hr,hc,ho,hor,hd,hb,hn,ht,hH,hV⟩:=OrientedSourceLabels318.source_oriented_labels w source
  exact ⟨⟨u,v,c,n,t,hu,hv,hr,hc,ho,hor,hd,hb,hn,ht,hH,hV⟩⟩

end
end SourceLabelData318
#print axioms SourceLabelData318.labels_exist
