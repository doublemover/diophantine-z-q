module
public import FourRootActualFiniteRamification318
public section
noncomputable section
namespace FourRootOffBranchRamification318
open scoped Classical
open Polynomial FourRootActualGenericField318 FourRootAffineTensorPresentation318
open FourRootActualFractionField318 FourRootActualResidueInertia318 FourRootNormalizedPointCharts318
variable (b:Fin 4→ℂ) (hb:Function.Injective b)
local instance polyAlgebra:Algebra P (A b):=
  (Polynomial.aeval (FourRootAffineCoordinateRing318.coordinate b none)).toAlgebra
local instance affineDomain:IsDomain (A b):=affine_domain b hb
local instance affineFinite:Module.Finite P (A b):=(FourRootActualOrderGalois318.finite_free b).1
local instance affineFlat:Module.Flat P (A b):=(FourRootActualOrderGalois318.finite_flat b).2
local instance groupFinite:Finite (FourRootActualOrderGalois318.G b):=
  FourRootActualOrderGalois318.group_finite b hb
local instance groupGalois:IsGaloisGroup (FourRootActualOrderGalois318.G b) P (A b):=
  FourRootActualOrderGalois318.galoisGroup b hb

lemma sign_one:FourRootActualOrderAutomorphisms318.polynomialSign b 1=1:=by
  have h:FourRootCoordinateRingSigns318.finiteEnd b 1=AlgHom.id ℂ (A b):=by
    apply FourRootAffineCoordinateRing318.hom_ext
    intro k
    cases k with
    | none=>simp [FourRootCoordinateRingSigns318.finite_base]
    | some i=>simp [FourRootCoordinateRingSigns318.finite_root,map_one]
  ext x
  rw [FourRootActualOrderAutomorphisms318.polynomialSign_apply]
  exact AlgHom.congr_fun h x

lemma all_signs_one (g:FourBinaryCharacters318.Group)
    (h:∀i,FourBinaryCharacters318.coordinate (F:=ℂ) i g=1):g=1:=by
  apply FourRootInertiaLabelCardinality318.signEquivalence.injective
  funext i
  have hi:FourBinaryCharacters318.signPattern g i=false:=
    (FourRootInertiaLabelCardinality318.coordinate_one_iff g i).mp (h i)
  have h1:FourBinaryCharacters318.signPattern (1:FourBinaryCharacters318.Group) i=false:=by
    simp [FourBinaryCharacters318.signPattern]
  exact hi.trans h1.symm

lemma regular_inertia_bot (p:FinitePoints b) (hp:∀j,p.val.1≠b j):
    (finitePrime b p).inertia (FourRootActualOrderGalois318.G b)=⊥:=by
  apply le_antisymm
  · intro e he
    change e=1
    obtain ⟨g,rfl⟩:=FourRootActualOrderAutomorphisms318.sign_surjective b hb e
    have hr:∀i,p.val.2 i≠0:=by
      intro i hi
      have hh:=p.property i
      rw [hi,zero_pow (by decide:2≠0)] at hh
      exact hp i (sub_eq_zero.mp hh.symm)
    have hc:∀i,FourBinaryCharacters318.coordinate (F:=ℂ) i g=1:=by
      have h:=(finite_sign_inertia b g p).mp
        ((FourRootFullFiniteInertia318.polynomial_inertia_iff b g p).mp he)
      exact fun i=>h i (hr i)
    rw [all_signs_one g hc]
    exact sign_one b
  · exact bot_le

@[expose] def pointBase (t:ℂ):Ideal P:=Ideal.span {X-C t}
lemma pointBase_maximal (t:ℂ):(pointBase t).IsMaximal:=
  FourRootActualFiniteRamification318.contact_maximal (fun _:Fin 4=>t) 0
lemma point_liesOver (p:FinitePoints b):(finitePrime b p).LiesOver (pointBase p.val.1):=by
  letI:(finitePrime b p).IsPrime:=finite_prime b p
  constructor
  apply (pointBase_maximal p.val.1).eq_of_le
    (Ideal.IsPrime.ne_top (inferInstance:((finitePrime b p).under P).IsPrime))
  apply Ideal.span_le.mpr
  intro r hr
  rcases Set.mem_singleton_iff.mp hr with rfl
  have he:finiteEvaluation b p (FourRootAffineCoordinateRing318.coordinate b none)=p.val.1:=
    congrArg (fun q:FinitePoints b=>q.val.1)
      ((FourRootAffineCoordinateRing318.pointEquiv b).apply_symm_apply p)
  change finiteEvaluation b p (Polynomial.aeval
    (FourRootAffineCoordinateRing318.coordinate b none) (X-C p.val.1))=0
  simp only [map_sub,Polynomial.aeval_X,Polynomial.aeval_C,AlgHom.commutes,he,
    Algebra.algebraMap_self,sub_self]
lemma point_separable (t:ℂ):Algebra.HasSeparableResidueFieldsAt P (A b) (pointBase t):=by
  letI:(pointBase t).IsPrime:=(pointBase_maximal t).isPrime
  letI:Algebra.IsIntegral P (A b):=Algebra.IsIntegral.of_finite P (A b)
  letI:Algebra ℂ (pointBase t).ResidueField:=
    ((algebraMap P (pointBase t).ResidueField).comp (algebraMap ℂ P)).toAlgebra
  letI:CharZero (pointBase t).ResidueField:=
    Algebra.charZero_of_charZero ℂ (pointBase t).ResidueField
  infer_instance

/-- Every actual finite point away from the four literal branches has
algebraic ramification index one. This excludes hidden extra branch
points by the full actual Galois inertia theorem. -/
theorem ramificationIdx_one (p:FinitePoints b) (hp:∀j,p.val.1≠b j):
    (finitePrime b p).ramificationIdx P=1:=by
  letI:(pointBase p.val.1).IsPrime:=(pointBase_maximal p.val.1).isPrime
  letI:(finitePrime b p).IsPrime:=finite_prime b p
  letI:(finitePrime b p).LiesOver (pointBase p.val.1):=point_liesOver b p
  letI:Algebra.HasSeparableResidueFieldsAt P (A b) (pointBase p.val.1):=point_separable b p.val.1
  have h:=Ideal.card_inertia_eq_ramificationIdxIn
    (G:=FourRootActualOrderGalois318.G b) (pointBase p.val.1) (finitePrime b p)
  rw [regular_inertia_bot b hb p hp] at h
  have hi:Ideal.ramificationIdxIn (pointBase p.val.1) (A b)=1:=by simpa using h.symm
  rw [←Ideal.ramificationIdxIn_eq_ramificationIdx (pointBase p.val.1) (finitePrime b p)
    (FourRootActualOrderGalois318.G b)]
  exact hi

theorem finite_exact_index (p:FinitePoints b):
    (finitePrime b p).ramificationIdx P=if ∃j,p.val.1=b j then 2 else 1:=by
  split_ifs with h
  · obtain ⟨j,hj⟩:=h
    exact FourRootActualFiniteRamification318.ramificationIdx_two b hb j p hj
  · exact ramificationIdx_one b hb p (by simpa only [not_exists] using h)
end FourRootOffBranchRamification318
