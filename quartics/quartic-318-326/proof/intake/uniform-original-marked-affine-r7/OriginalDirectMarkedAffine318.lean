module
public import OriginalWholeAffineSections318
public import OriginalOneRawMarkedGenerator318
public import OriginalUnramifiedMarkedCoordinate318
public import OriginalMarkedTraitsHeight318
import all SelectedActualSameAFiniteDlogRows318
import all OriginalIntegralFrameLocalize318
import all OriginalKleinPrimitivePair318
import all OriginalMarkedChartSpecialization318
public section
noncomputable section
namespace OriginalDirectMarkedAffine318
open OriginalMarkedChartSpecialization318 OriginalMarkedTraitInverse318 OriginalOneRawMarkedGenerator318
open OriginalWholeAffineSections318 OriginalIntegerAffineExtend318 OriginalIntegralFrameLocalize318
open OriginalKleinPrimitivePair318 SelectedSameADirectBicanonicalHeight318
open SelectedActualSameAFiniteDlogRows318 SelectedSameADyadicVerticalD2_318
open scoped TensorProduct Pointwise
variable {K E S H : Type} [Field K] [CharZero K] [Field E] [CharZero E] [CommRing S]
    [Algebra S E] [AddCommGroup H] [Module S H]

/-- At a genuine horizontal mark on the generic curve, the actual
derivation on K associated to the integral dualizing frame restricts to
the *actual* ordinary mark stalk. No derivative of t as a number in E. -/
def stalkD (A V:Subring K) [IsFractionRing A K] (incl:A≤V) (m:Ideal A) [m.IsPrime]
    (loc:letI := (Subring.inclusion incl).toAlgebra; IsLocalization m.primeCompl V)
    (fr:KaehlerDifferential ℤ A→ₗ[A]A) : Derivation ℤ V V :=
  restrictD V (fractionDerivative A fr) (preserves_stalk A m V incl loc (fractionDerivative A fr)
    (fun z hz => by
      let a:A:=⟨z,hz⟩
      change fractionDerivative A fr (a:K)∈A
      rw [fractionDerivative_apply]; exact (fr (KaehlerDifferential.D ℤ A a)).property))

omit [CharZero K] in
theorem actualD (A V:Subring K) [IsFractionRing A K] (incl:A≤V) (m:Ideal A) [m.IsPrime]
    (loc:letI := (Subring.inclusion incl).toAlgebra; IsLocalization m.primeCompl V)
    (fr:KaehlerDifferential ℤ A→ₗ[A]A) (T:V) :
    ((stalkD A V incl m loc fr T:V):K)=fractionDerivative A fr (T:K) := by
  rfl

/-- Direct original-source constructor. Normal arithmetic affine (as a subring
of its true function field), Dedekind rational fibre, reduced vertical
fibres, marked raw KS and original character functions suffice. NO per-DVR
frame data, semilocal tuple, explicit Néron chart, constant extension,
primitive elliptic form, prechosen regular bicanonical pair or equality on
all generic Hodge tensors is supplied. The map to E is ONLY on the
actual mark stalk, as it must be. -/
theorem marked (A:Subring K) [IsFractionRing A K] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (G:Subalgebra ℚ K) [IsFractionRing G K] [IsDedekindDomain G] (ag:A≤G.toSubring)
    (gen:letI := (Subring.inclusion ag).toAlgebra; IsLocalization (positiveIntegers A) G)
    (red:∀p:ℕ,p.Prime→IsReduced (A⧸Ideal.span ({(p:A)}:Set A)))
    (V:Subring K) (av:A≤V) (mA:Ideal A) [mA.IsPrime]
    (loc:letI := (Subring.inclusion av).toAlgebra; IsLocalization mA.primeCompl V)
    (ev:V→+*E) (fr:KaehlerDifferential ℤ A→ₗ[A]A) (T:V) (q:ℚ) (qt:ev T=(q:E))
    (np:P (q:E)≠0)
    (r:Fin 4→K) (twist:Fin 4→ℚˣ)
    (he:∀i,(r i)^2=algebraMap ℚ K (twist i:ℚ)*contact (T:K) i)
    {m:Ideal S} [m.IsPrime] [Algebra A (Localization.AtPrime m)] [Algebra (Localization.AtPrime m) E]
    [IsScalarTower S (Localization.AtPrime m) E]
    (comm:(algebraMap (Localization.AtPrime m) E).comp (algebraMap A (Localization.AtPrime m))
      =ev.comp (Subring.inclusion av))
    {L:Type} [AddCommGroup L] [Module A L] (φ:L→ₗ[A]A) (univ:φ.range=(210:A) • (⊤:Submodule A A))
    (pull:Localization.AtPrime m⊗[S]H≃ₗ[Localization.AtPrime m]Localization.AtPrime m⊗[A]L)
    (bas:Localization.AtPrime m⊗[S]H≃ₗ[Localization.AtPrime m]Localization.AtPrime m) (F:H→ₗ[S]E)
    (one:algebraMap (Localization.AtPrime m) E (pullRaw φ pull (bas.symm 1))=
      (ev (stalkD A V av mA loc fr T))^2*OriginalHodgeModuleOverlap318.read F (bas.symm 1)) :
    Nonempty (Chart F (fun i=>coefficients (F:=E) q i/P (q:E)) m) := by
  have nb : ev (stalkD A V av mA loc fr T)≠0 := by
    have live := survives (E:=E) (pullRaw φ pull) bas (image φ pull univ)
    rw [one] at live
    intro h
    rw [h,zero_pow (by decide : 2≠0),zero_mul] at live
    exact live rfl
  have nV : pRing T≠0 := by
    intro h; apply np
    change pRing (q:E)=0
    rw [←qt,←map_p, h,map_zero]
  have nK : P (T:K)≠0 := by
    change pRing (V.subtype T)≠0
    rw [←map_p V.subtype T]
    exact fun h => nV ((show Function.Injective V.subtype from Subtype.val_injective) (h.trans (map_zero V.subtype).symm))
  have ep : SelectedActualSameAFiniteDlogRows318.product (T:K)=P (T:K) := by
    norm_num [SelectedActualSameAFiniteDlogRows318.product,contact,P,LinearContactSquareclass318.contacts]
  have npr : SelectedActualSameAFiniteDlogRows318.product (T:K)≠0 := ep ▸ nK
  change contact (T:K) 0*contact (T:K) 1*contact (T:K) 2*contact (T:K) 3≠0 at npr
  have hn (i:Fin 4) : contact (T:K) i≠0 := by
    fin_cases i
    · exact left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul npr))
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul npr))
    · exact right_ne_zero_of_mul (left_ne_zero_of_mul npr)
    · exact right_ne_zero_of_mul npr
  let D := fractionDerivative A fr
  let β := stalkD A V av mA loc fr T
  have jet : (β:K)=D (T:K) := actualD A V av mA loc fr T
  obtain ⟨hx,hy⟩ := produce A G ag gen red fr (T:K) r twist hn he
  let z : A := ⟨_,hx⟩
  let w : A := ⟨_,hy⟩
  have e0 : (z:K)=205800*(β:K)^2/P (T:K) := by
    change (25725/4:K)*32*qcoeff (T:K) (D (T:K))=_
    rw [qcoeff,ep,jet]; ring
  have e1 : (w:K)=(25725/4)*(T:K)*(β:K)^2/P (T:K) := by
    change (25725/4:K)*(T:K)*qcoeff (T:K) (D (T:K))=_
    rw [qcoeff,ep,jet]; ring
  have h := evaluate (Subring.inclusion av) V.subtype Subtype.val_injective ev T β q qt nb np z w e0 e1 nK
  let U := Localization.AtPrime m
  let inc : U→ₐ[S]E := IsScalarTower.toAlgHom S U E
  refine ⟨{
    A:=A,ring:=inferInstance,mark:=algebraMap A U,raw:=pullRaw φ pull,
    read:=((ev β)^2)⁻¹ • inc.toLinearMap,generic:=?_,image_eq:=image φ pull univ,
    sectionValue:=![z,w],same:=?_ }⟩
  · intro a
    change ((ev β)^2)⁻¹*algebraMap U E (pullRaw φ pull (1⊗ₜ[S]a))=F a
    rw [covariance F (pullRaw φ pull) bas _ one]; dsimp only [β]; field_simp [nb]
  · intro i
    have agree (a:A) : algebraMap U E (algebraMap A U a)=ev (Subring.inclusion av a) :=
      DFunLike.congr_fun comm a
    change ((ev β)^2)⁻¹*algebraMap U E (algebraMap A U (![z,w] i))=_
    rw [agree,mul_comm,←div_eq_mul_inv]
    exact h i
end OriginalDirectMarkedAffine318
