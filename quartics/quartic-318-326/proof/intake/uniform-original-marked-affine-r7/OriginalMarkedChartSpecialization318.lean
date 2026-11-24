module
public import OriginalMarkedTraitInverse318
public import OriginalKleinPrimitivePair318
import all OriginalKleinPrimitivePair318
import Mathlib.Tactic
public section
noncomputable section
namespace OriginalMarkedChartSpecialization318
open OriginalKleinPrimitivePair318 SelectedSameADirectBicanonicalHeight318
open scoped TensorProduct Pointwise

/-- Four branch factors as elements of a MARK STALK, where T is finite;
the marked bicanonical sections may have other presentations on the
original integral chart. No inverse of 4 or of P in this stalk is used. -/
def pRing {A : Type*} [CommRing A] (t:A) := t*(t-32)*(t-76832)*(t+343)

theorem map_p {A B : Type*} [CommRing A] [CommRing B] (j:A→+*B) (t:A) :
    j (pRing t) = pRing (j t) := by simp only [pRing,map_mul,map_add,map_sub,map_ofNat]

/-- Read integral outputs of the structural proof at the finite mark.
A is the original model affine, G its characteristic-zero mark stalk.
Only G, NOT the function field K, may be specialized in E. The integral
specialized chart tensor is read in (dT)², not in an arbitrary local basis. -/
theorem evaluate {A G K E : Type*} [CommRing A] [CommRing G] [Field K] [CharZero K]
    [Field E] [CharZero E] (g:A→+*G) (j:G→+*K) (inj:Function.Injective j) (ev:G→+*E)
    (T β:G) (q:ℚ) (qt:ev T=(q:E)) (nb:ev β≠0) (np:P (q:E)≠0)
    (z0 z1:A) (h0:j (g z0)=205800*(j β)^2/P (j T))
    (h1:j (g z1)=(25725/4)*j T*(j β)^2/P (j T)) (nP:P (j T)≠0) :
    ∀i:Fin 2,ev (g (![z0,z1] i))/(ev β)^2=coefficients (F:=E) q i/P (q:E) := by
  have z0eq : g z0*pRing T=205800*β^2 := by
    apply inj
    simp only [map_mul,map_p,map_ofNat,map_pow]
    exact (eq_div_iff nP).mp h0
  have z1eq : 4*g z1*pRing T=25725*T*β^2 := by
    apply inj
    simp only [map_mul,map_p,map_ofNat,map_pow]
    change 4*j (g z1)*P (j T)=_
    rw [h1]
    field_simp [nP]
  have eq0 := congrArg ev z0eq
  have eq1 := congrArg ev z1eq
  simp only [map_mul,map_p,map_ofNat,map_pow,qt] at eq0 eq1
  change ev (g z0)*P (q:E)=_ at eq0
  change 4*ev (g z1)*P (q:E)=_ at eq1
  intro i; fin_cases i
  · change ev (g z0)/(ev β)^2=coefficientScale E*32/P (q:E)
    have h : coefficientScale E*32=205800 := by norm_num [coefficientScale]
    rw [h]; field_simp [np,nb]; linear_combination eq0
  · change ev (g z1)/(ev β)^2=coefficientScale E*(q:E)/P (q:E)
    have h : coefficientScale E=(25725:E)/4 := by norm_num [coefficientScale]
    rw [h]; field_simp [np,nb]; linear_combination eq1

/-- On the trait, take the universal original raw KS map, base-change even
along a nonflat mark, and transport along the true Hodge pullback. With an
affine dualizing frame the target is literally the local ring. -/
def pullRaw {A U H L : Type*} [CommRing A] [CommRing U] [Algebra A U] [AddCommGroup H]
    [Module A H] [AddCommGroup L] [Module U L] (φ:H→ₗ[A]A) (pull:L≃ₗ[U]U⊗[A]H) :
    L→ₗ[U]U := (TensorProduct.AlgebraTensorModule.rid A U U).toLinearMap.comp
      ((φ.baseChange U).comp pull.toLinearMap)

theorem image {A U H L : Type*} [CommRing A] [CommRing U] [Algebra A U] [AddCommGroup H]
    [Module A H] [AddCommGroup L] [Module U L] (φ:H→ₗ[A]A) (pull:L≃ₗ[U]U⊗[A]H)
    (univ:φ.range=(210:A) • (⊤:Submodule A A)) :
    (pullRaw φ pull).range=(210:U) • (⊤:Submodule U U) := by
  let e := TensorProduct.AlgebraTensorModule.rid A U U
  have bc := OriginalRawImageOnMark318.baseChange (S:=U) φ 210 univ
  rw [map_ofNat] at bc
  apply le_antisymm
  · rintro _ ⟨h,rfl⟩
    obtain ⟨k,_,hk⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp
      (bc ▸ LinearMap.mem_range_self (φ.baseChange U) (pull h))
    change e ((φ.baseChange U) (pull h)) ∈ _
    rw [←hk,map_smul]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  · intro v hv
    obtain ⟨b,_,hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv
    obtain ⟨k,hk⟩ : (210:U) • e.symm b ∈ (φ.baseChange U).range := by
      rw [bc]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
    refine ⟨pull.symm k,?_⟩
    change e ((φ.baseChange U) (pull (pull.symm k)))=v
    rw [pull.apply_symm_apply,hk,map_smul,e.apply_symm_apply,hb]

end OriginalMarkedChartSpecialization318
