module
public import OriginalGluedCechRestriction318
public section
noncomputable section
namespace OriginalGluedCechTrace318
open Polynomial OriginalSparseQuadraticCharts318 OriginalActualQuadraticLaurent318
open OriginalGluedDualizingTransition318 OriginalGluedCechRestriction318 OriginalGlobalDualizingClass318
open OriginalGlobalP1Residue318
variable {E:Type*} [Field E]

@[expose] def trace (f:E[X]) (z:Overlap f) : E :=
  res (OriginalQuadraticDualizing318.toDual (toLaurent f) (up f z) 1)
@[expose] def finite (s t:E) (a b:E[X]) : Overlap (F s t) :=
  down _ (construct (F s t) (cu a) (cu b))
@[expose] def infinity (s t:E) (p q:E[X]) : Overlap (F s t) :=
  down _ (-(inc (F s t) (LaurentPolynomial.T 1)*move s t (construct (G s t) (cu p) (cu q))))
@[expose] def pull (f:E[X]) (h:LaurentPolynomial E) : Overlap f :=
  down f (construct f 0 (2*h))

theorem read (f:E[X]) (a b:LaurentPolynomial E) :
    trace f (down f (construct f a b))=res b := by
  have e:=AlgHom.congr_fun (up_down f) (construct f a b)
  change up f (down f (construct f a b))=construct f a b at e
  rw [trace,e,OriginalGluedCechRestriction318.eval_one]

theorem joint (s t:E) (a b p q:E[X]) :
    finite s t a b+infinity s t p q=
      down (F s t) (construct (F s t) (cu a+cvOdd p) (cu b+cv q)) := by
  rw [finite,infinity,restricted,←map_add]
  congr 1
  unfold construct
  rw [map_add,map_add,add_mul]; ring

/-- Precisely the zero-trace regular differential cocycles on the actual
localized ring are coboundaries of its two affine sections. Both directions
use the same localization maps as the algebraic gluing. -/
theorem iff_boundary (s t:E) (z:Overlap (F s t)) : trace _ z=0 ↔
    ∃ a b p q:E[X], z=finite s t a b+infinity s t p q := by
  constructor
  · intro h
    obtain ⟨r,u,e⟩:=everyone (F s t) (up (F s t) z)
    have hz: down (F s t) (construct (F s t) r u)=z := by
      rw [e]; exact AlgHom.congr_fun (down_up (F s t)) z
    have hr : res u=0 := (read _ _ _).symm.trans (hz ▸ h)
    obtain ⟨a,p,ha⟩:=odd_exact r
    obtain ⟨b,q,hb⟩:=(exact_cech u).mp hr
    exact ⟨a,b,p,q,by rw [joint,←ha,←hb,hz]⟩
  · rintro ⟨a,b,p,q,rfl⟩
    rw [joint,read,res_add,(chart_zero b).1,(chart_zero q).2,add_zero]

theorem read_pull (f:E[X]) (h:LaurentPolynomial E) : trace f (pull f h)=2*res h := by
  rw [pull,read,two_mul,res_add,two_mul]

end OriginalGluedCechTrace318
#print axioms OriginalGluedCechTrace318.iff_boundary
#print axioms OriginalGluedCechTrace318.read_pull
