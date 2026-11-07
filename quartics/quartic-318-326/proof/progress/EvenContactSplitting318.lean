module
public import EvenContactEtale318
public import EvenContactHensel318
public import Mathlib.Algebra.Polynomial.RingDivision
public section
noncomputable section
namespace EvenContactSplitting318
open Polynomial EvenContactEtale318
set_option maxHeartbeats 0
variable {R:Type*} [CommRing R]

@[expose] def evaluateRoot (u:Rˣ) (r:R) (hr:r^2=(u:R)) : RootRing u→ₐ[R]R :=
  AdjoinRoot.liftAlgHom (polynomial u) (AlgHom.id R R) r (by
    simpa [polynomial,eval₂_sub,eval₂_pow,eval₂_X,eval₂_C] using sub_eq_zero.mpr hr)

@[simp] theorem evaluateRoot_root (u:Rˣ) (r:R) (hr:r^2=(u:R)) :
    evaluateRoot u r hr (root u)=r :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[expose] def evaluationPair (u:Rˣ) (r:R) (hr:r^2=(u:R)) : RootRing u→ₐ[R]R×R :=
  (evaluateRoot u r hr).prod (evaluateRoot u (-r) (by simpa using hr))

@[simp] theorem evaluationPair_root (u:Rˣ) (r:R) (hr:r^2=(u:R)) :
    evaluationPair u r hr (root u)=(r,-r) := by
  simp [evaluationPair]

@[simp] theorem evaluateRoot_mk (u:Rˣ) (r:R) (hr:r^2=(u:R)) (p:R[X]) :
    evaluateRoot u r hr (AdjoinRoot.mk (polynomial u) p)=p.eval r := by
  simp [evaluateRoot,AdjoinRoot.liftAlgHom_mk]

theorem evaluationPair_injective (u:Rˣ) (r:R) (hr:r^2=(u:R))
    (h2:IsUnit (2:R)) : Function.Injective (evaluationPair u r hr) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨p,rfl⟩:=AdjoinRoot.mk_surjective (g:=polynomial u) x
  have hp:p.eval r=0 := by
    have hh:=congrArg Prod.fst hx
    simpa [evaluationPair] using hh
  have hm:p.eval (-r)=0 := by
    have hh:=congrArg Prod.snd hx
    simpa [evaluationPair] using hh
  have hur:IsUnit r := (isUnit_pow_iff (by decide:2≠0)).mp (hr.symm ▸ u.isUnit)
  have hc:IsCoprime (X-C r) (X-C (-r)) :=
    isCoprime_X_sub_C_of_isUnit_sub (by simpa [sub_neg_eq_add,←two_mul] using h2.mul hur)
  have hd:(X-C r)*(X-C (-r))∣p :=
    hc.mul_dvd ((dvd_iff_isRoot).mpr hp) ((dvd_iff_isRoot).mpr hm)
  have hf:(X-C r)*(X-C (-r))=polynomial u := by
    simp only [map_neg,sub_neg_eq_add,polynomial]
    rw [←hr,map_pow]
    ring
  rw [hf] at hd
  exact AdjoinRoot.mk_eq_zero.mpr hd

theorem evaluationPair_surjective (u:Rˣ) (r:Rˣ) (hr:(r:R)^2=(u:R))
    (v:Rˣ) (hv:(v:R)=2) : Function.Surjective (evaluationPair u (r:R) hr) := by
  rintro ⟨x,y⟩
  let a:R:=(x+y)*(↑v⁻¹:R)
  let b:R:=(x-y)*(↑v⁻¹:R)*(↑r⁻¹:R)
  refine ⟨algebraMap R (RootRing u) a+algebraMap R (RootRing u) b*root u,?_⟩
  have hi:(2:R)*(↑v⁻¹:R)=1 := by rw [←hv]; exact Units.mul_inv v
  have hbr:b*(r:R)=(x-y)*(↑v⁻¹:R) := by
    dsimp [b]
    rw [mul_assoc,Units.inv_mul,mul_one]
  apply Prod.ext
  · change evaluateRoot u (r:R) hr _=x
    simp only [map_add,map_mul,AlgHom.commutes,evaluateRoot_root]
    change a+b*(r:R)=x
    rw [hbr]
    dsimp [a]
    linear_combination x*hi
  · change evaluateRoot u (-(r:R)) _ _=y
    simp only [map_add,map_mul,AlgHom.commutes,evaluateRoot_root]
    change a+b*(-(r:R))=y
    rw [mul_neg,hbr]
    dsimp [a]
    linear_combination y*hi

@[expose] def splitEquiv (u:Rˣ) (r:Rˣ) (hr:(r:R)^2=(u:R))
    (v:Rˣ) (hv:(v:R)=2) : RootRing u≃ₐ[R]R×R :=
  AlgEquiv.ofBijective (evaluationPair u (r:R) hr)
    ⟨evaluationPair_injective u r hr (hv ▸ v.isUnit),evaluationPair_surjective u r hr v hv⟩

@[simp] theorem splitEquiv_root (u:Rˣ) (r:Rˣ) (hr:(r:R)^2=(u:R))
    (v:Rˣ) (hv:(v:R)=2) : splitEquiv u r hr v hv (root u)=((r:R),-(r:R)) :=
  evaluationPair_root u r hr

/-- The actual unit-root cover splits over a strict Henselian local ring away
from residue characteristic two. No splitting or root is supplied. -/
theorem strictHenselian_split [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (u:Rˣ) (h2:(2:IsLocalRing.ResidueField R)≠0) :
    ∃r:Rˣ, (r:R)^2=(u:R) ∧ ∃e:RootRing u≃ₐ[R]R×R,
      e (root u)=((r:R),-(r:R)) := by
  obtain ⟨a,ha,hu⟩:=EvenContactHensel318.unit_square_root u h2
  obtain ⟨r,hr⟩:=hu
  subst a
  have ht:IsUnit (2:R):=(IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    (by simpa only [map_ofNat] using h2)
  obtain ⟨v,hv⟩:=ht
  exact ⟨r,ha,splitEquiv u r ha v hv,splitEquiv_root u r ha v hv⟩

/-- The splitting tracks the actual even-contact root on both components. -/
theorem splitEquiv_even_contact_root (u:Rˣ) (r:Rˣ) (hr:(r:R)^2=(u:R))
    (v:Rˣ) (hv:(v:R)=2) (pi:R) (k:ℕ) :
    splitEquiv u r hr v hv (root u*algebraMap R (RootRing u) pi^k)=
      ((r:R)*pi^k,-(r:R)*pi^k) := by
  rw [map_mul,map_pow,AlgEquiv.commutes,splitEquiv_root]
  rfl

/-- Actual finite even DVR valuation yields a decomposition and a split normalized
cover. Neither the unit decomposition nor the splitting is supplied. -/
theorem dvr_even_contact_split [HenselianLocalRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (h2:(2:IsLocalRing.ResidueField R)≠0) (x:R) (k:ℕ)
    (hx:IsDiscreteValuationRing.addVal R x=((2*k:ℕ):ℕ∞)) :
    ∃pi:R, Irreducible pi ∧ ∃u:Rˣ, x=(u:R)*pi^(2*k) ∧
      ∃r:Rˣ, (r:R)^2=(u:R) ∧ ∃e:RootRing u≃ₐ[R]R×R,
        e (root u*algebraMap R (RootRing u) pi^k)=
          ((r:R)*pi^k,-(r:R)*pi^k) := by
  have hx0:x≠0 := by
    intro hz
    rw [hz,IsDiscreteValuationRing.addVal_zero] at hx
    exact ENat.top_ne_natCast (2*k) hx
  obtain ⟨pi,hpi⟩:=IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n,u,hu⟩:=IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hpi
  have hn:n=2*k := by
    have hh:=IsDiscreteValuationRing.addVal_def x u hpi n hu
    rw [hh] at hx
    exact_mod_cast hx
  subst n
  obtain ⟨r,hr,e,he⟩:=strictHenselian_split u h2
  refine ⟨pi,hpi,u,hu,r,hr,e,?_⟩
  rw [map_mul,map_pow,AlgEquiv.commutes,he]
  rfl

end EvenContactSplitting318
