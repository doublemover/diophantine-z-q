module
public import RawAnchorNorm318
public import KummerAlgebra318
public section
namespace RawScalarKummer318
open CircuitReplay Raw318FinalReplay ConcreteG8Domain LocalGenerator318 KummerAlgebra318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem scalar_kummer (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    (RawAnchorNorm318.root w 1*RawAnchorNorm318.scalarRoot w)^2-
      xP*(RawAnchorNorm318.scalarRoot w)^2-
      2*jP*RawAnchorNorm318.root w 1*RawAnchorNorm318.scalarRoot w-
      xP*(RawAnchorNorm318.root w 1)^2-D=0 := by
  have h270 : r270 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=270)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r270] at h270
  have h271 : r271 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=271)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r271] at h271
  have h272 : r272 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=272)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r272] at h272
  have h273 : r273 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=273)
    (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [r273] at h273
  have hp : RawAnchorNorm318.root w 1*RawAnchorNorm318.scalarRoot w=pair (w 305) (w 306) := by
    change pair (w 82) (w 83)*pair (w 303) (w 304)=_
    ext <;> norm_num [pair] <;> [linear_combination -h270;linear_combination -h271]
  have hr : 2*jP*RawAnchorNorm318.root w 1*RawAnchorNorm318.scalarRoot w=
      2*jP*(RawAnchorNorm318.root w 1*RawAnchorNorm318.scalarRoot w) := by ring
  rw [hr,hp]
  change (pair (w 305) (w 306))^2-xP*(pair (w 303) (w 304))^2-
    2*jP*pair (w 305) (w 306)-xP*(pair (w 82) (w 83))^2-D=0
  ext <;> norm_num [xP,jP,D,i,pair,pow_succ] <;>
    [linear_combination h272;linear_combination h273]

end RawScalarKummer318
