module
public import OriginalSparsePolynomialReflection318
public section
noncomputable section
namespace OriginalUniversalSparseCoefficients318
open Polynomial OriginalUniversalSparsePolynomial318 OriginalSparsePolynomialReflection318
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
@[expose] def read {K : Type*} [CommRing K] (s t : K) (l : Tri) : K[X] :=
  pol (l.map (co s t))
theorem co_C {K : Type*} [CommRing K] (s t : K) (p : Co) :
    C (co s t p)=co (C s) (C t) p := by
  have h (l : List ℤ) : C (value (Int.castRingHom K) s l)=
      value (Int.castRingHom K[X]) (C s) l := by
    induction l with
    | nil => simp [value]
    | cons c l ih =>
      simp only [value,map_add,map_mul]
      rw [ih]; simp
  induction p with
  | nil => simp [co,value]
  | cons c p ih =>
    change C (value (Int.castRingHom K) s c + t*co s t p)=_
    simp only [map_add,map_mul,h,ih]
    rfl
theorem read_eq {K : Type*} [CommRing K] (s t : K) (p : Tri) :
    read s t p=tri (C s) (C t) X p := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    change C (co s t c)+X*read s t p = co (C s) (C t) c+X*tri (C s) (C t) X p
    rw [co_C,ih]
@[expose] def ff : Tri := [[[],[],[125],[0,-75],[0,0,15],[0,0,0,-1]],[[],[],[0,-50],[0,0,20],[0,0,0,-2]],[],[[],[0,50],[0,0,-10]],[],[[],[0,0,-2]],[[0,0,1]]]
@[expose] def df : Tri := [[[],[],[0,-50],[0,0,20],[0,0,0,-2]],[],[[],[0,150],[0,0,-30]],[],[[],[0,0,-10]],[[0,0,6]]]
@[expose] def gs : Tri := [[[],[],[],[-75],[0,30],[0,0,-3]],[[],[],[-50],[0,40],[0,0,-6]],[],[[],[50],[0,-20]],[],[[],[0,-4]],[[0,2]]]
@[expose] def gt : Tri := [[[],[250],[0,-225],[0,0,60],[0,0,0,-5]],[[],[0,-100],[0,0,60],[0,0,0,-8]],[],[[0,50],[0,0,-20]],[],[[0,0,-2]],[]]
@[expose] def de : Tri := [[[],[],[],[0,-27000000000],[0,0,32850000000,625000000],[0,0,625000000,-16730000000,-625000000],[0,0,0,-625000000,4564000000,250000000],[0,0,0,0,250000000,-703200000,-50000000],[0,0,0,0,0,-50000000,58000000,5000000],[0,0,0,0,0,0,5000000,-2000000,-200000],[0,0,0,0,0,0,0,-200000]]]
@[expose] def onePoly : Tri := [[[1]]]
theorem read_F {K : Type*} [CommRing K] (s t : K) : read s t ff=sextic s t := by
  simp [read,ff,co,value,sextic,cvec,pol,C_ofNat]; ring
theorem read_dF {K : Type*} [CommRing K] (s t : K) : read s t df=(sextic s t).derivative := by
  simp only [sextic,cvec,pol,derivative_add,derivative_C,derivative_X,derivative_mul,derivative_zero]
  simp [read,df,co,value,pol,C_ofNat]; ring
theorem read_gS {K : Type*} [CommRing K] (s t : K) : read s t gs=pol (gS s t) := by
  simp [read,gs,co,value,gS,pol,C_ofNat]; ring
theorem read_gT {K : Type*} [CommRing K] (s t : K) : read s t gt=pol (gT s t) := by
  simp [read,gt,co,value,gT,pol,C_ofNat]; ring
theorem read_den {K : Type*} [CommRing K] (s t : K) : read s t de=C (denom s t) := by
  simp [read,de,co,value,denom,core,pol,C_ofNat]; ring
theorem read_one {K : Type*} [CommRing K] (s t : K) : read s t onePoly=1 := by
  simp [read,onePoly,co,value,pol]
@[expose] def shift : ℕ → Tri → Tri
  | 0,p => p
  | k+1,p => []::shift k p
theorem read_shift {K : Type*} [CommRing K] (s t : K) (k : ℕ) (p : Tri) :
    read s t (shift k p)=X^k * read s t p := by
  induction k with
  | zero => simp [shift]
  | succ k ih =>
    change C 0+X*read s t (shift k p)=_
    rw [ih]; simp [pow_succ]; ring
end OriginalUniversalSparseCoefficients318
