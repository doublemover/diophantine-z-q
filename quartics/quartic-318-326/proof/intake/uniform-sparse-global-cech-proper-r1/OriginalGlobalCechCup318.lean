module
public import OriginalGlobalCechOverlap318
public section
noncomputable section
namespace OriginalGlobalCechCup318
open Polynomial OriginalSeparableSexticJet318 OriginalGlobalCechOverlap318
open OriginalGlobalCechRemainder318
variable {E S:Type*} [Field E] [CommRing S] [Algebra E S]
@[expose] def u (J:Data E) (x y c:S) : S := -c*y*aeval x J.inverse_quotient
@[expose] def v (J:Data E) (x:S) : S := aeval x J.inverse
theorem bezout (J:Data E) (x y c:S) (hy:y^2=aeval x J.F) (hc:2*c=1) :
    u J x y c*(2*y)+v J x*(aeval x J.F.derivative)=1 := by
  have e:=congrArg (aeval x) J.inverse_relation
  simp only [map_mul,map_sub,map_one] at e
  unfold u v
  linear_combination e-(aeval x J.inverse_quotient)*hy-
    (y^2*aeval x J.inverse_quotient)*hc

/-- The adjunction generator ξ=dx/(2y)=dy/F′ is a genuine *globally regular
affine Kähler form*, expressed everywhere by polynomial coefficients. -/
@[expose] def xi (J:Data E) (x y c:S) : Ω[S⁄E] :=
  u J x y c • KaehlerDifferential.D E S x+v J x • KaehlerDifferential.D E S y

theorem coframe (J:Data E) (x y c:S) (hy:y^2=aeval x J.F) (hc:2*c=1) :
    (2*y) • xi J x y c=KaehlerDifferential.D E S x ∧
    aeval x J.F.derivative • xi J x y c=KaehlerDifferential.D E S y := by
  let dx:=KaehlerDifferential.D E S x
  let dy:=KaehlerDifferential.D E S y
  let fp:=aeval x J.F.derivative
  let a:=u J x y c
  let b:=v J x
  have hr : (2*y)•dy=fp•dx := OriginalBranchCechCalculus318.kahler J.F x y hy
  have he : a*(2*y)+b*fp=1 := bezout J x y c hy hc
  change (2*y)•(a•dx+b•dy)=dx ∧ fp•(a•dx+b•dy)=dy
  constructor
  · rw [smul_add,smul_comm (2*y) a,smul_comm (2*y) b,hr,smul_smul,smul_smul,
      ←add_smul,he,one_smul]
  · rw [smul_add,smul_comm fp a,smul_comm fp b,←hr,smul_smul,smul_smul,
      ←add_smul,he,one_smul]

/-- Contract the *literal* two-chart cocycle with (dx/y)^2. The two factors of
2 come from ω=2ξ and cancel 1/2 in the vector. No localization at y is taken. -/
theorem contraction (J:Data E) (q:E[X]) (hq : J.G-J.remainder 0*J.F.derivative=J.F*q)
    (x:Sˣ) (y c:S) (hy:y^2=aeval (x:S) J.F) (hc:2*c=1) (k:Fin 3) :
    let Z:=splittingCertificate J
    let z:S:=x
    let iv:S:=↑x⁻¹
    let w:=y*iv^3
    let dv:=aeval iv (reflect 5 (P Z))
    let dw:=c*w*aeval iv (reflect 4 (Qstar Z q))
    let tx:= -aeval z (J.remainder 0)-(-z^2*dv)
    let ty:= c*y*aeval z q-(z^3*dw-3*y*z*dv)
    (z^(k:ℕ)*(2*(u J z y c*tx+v J z*ty))) • ((2:S) • xi J z y c)=
      LaurentPolynomial.eval₂ (algebraMap E S) x (form Z k) • KaehlerDifferential.D E S z := by
  let Z:=splittingCertificate J
  have hh := difference Z q hq x y c hy hc
  dsimp only at hh ⊢
  rw [←show Z=splittingCertificate J by rfl]
  rw [show J.remainder 0=Z.remainder 0 by rfl,hh.1,hh.2,form_eval,smul_smul]
  have he:=bezout J (x:S) y c hy hc
  have hs:= (coframe J (x:S) y c hy hc).1
  rw [←hs,smul_smul]
  congr 1
  rw [show Z.F=J.F by rfl]
  linear_combination -(x:S)^(k:ℕ)*4*c*y*aeval (x:S) (A Z)*(↑x⁻¹:S)^3*he-
    2*(x:S)^(k:ℕ)*y*(aeval (x:S) (A Z))*(↑x⁻¹:S)^3*hc
end OriginalGlobalCechCup318
#print axioms OriginalGlobalCechCup318.coframe
#print axioms OriginalGlobalCechCup318.contraction
