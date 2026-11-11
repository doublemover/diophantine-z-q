module
public import FourRootCoordinateRingSigns318
public section
noncomputable section
namespace FourRootActionStabilizers318
open FourBinaryCharacters318 FourRootNormalizedPointCharts318
open FourRootNormalizedSignAction318
variable (b:Fin 4→ℂ)

lemma action_one (p:Completed b):action b 1 p=p:=by
  rcases p with p|s
  · apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext rfl
    funext i
    simp [finite,map_one]
  · apply congrArg Sum.inr
    apply Subtype.ext
    funext i
    simp [signs,map_one]

lemma action_mul (g h:FourBinaryCharacters318.Group) (p:Completed b):
    action b (g*h) p=action b g (action b h p):=by
  rcases p with p|s
  · apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext rfl
    funext i
    change coordinate (F:=ℂ) i (g*h)*p.val.2 i=
      coordinate (F:=ℂ) i g*(coordinate (F:=ℂ) i h*p.val.2 i)
    rw [map_mul,mul_assoc]
  · apply congrArg Sum.inr
    apply Subtype.ext
    funext i
    change coordinate (F:=ℂ) i (g*h)*coordinate (F:=ℂ) 0 (g*h)*s.val i=
      coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g*
        (coordinate (F:=ℂ) i h*coordinate (F:=ℂ) 0 h*s.val i)
    simp only [map_mul]
    ring

/-- Stabilizers are computed in the independent original root equations,
not inferred from the degree of the covering. -/
lemma finite_fixed_iff (g:FourBinaryCharacters318.Group) (p:FinitePoints b):
    finite b g p=p ↔ ∀i,p.val.2 i≠0→coordinate (F:=ℂ) i g=1:=by
  constructor
  · intro h i hi
    have he:=congrArg (fun q:FinitePoints b=>q.val.2 i) h
    change coordinate (F:=ℂ) i g*p.val.2 i=p.val.2 i at he
    exact mul_right_cancel₀ hi (by simpa using he)
  · intro h
    apply Subtype.ext
    apply Prod.ext rfl
    funext i
    change coordinate (F:=ℂ) i g*p.val.2 i=p.val.2 i
    by_cases hi:p.val.2 i=0
    · rw [hi,mul_zero]
    · rw [h i hi,one_mul]

lemma finite_branch_fixed_iff (hb:Function.Injective b)
    (g:FourBinaryCharacters318.Group) (j:Fin 4) (p:FinitePoints b)
    (hp:p.val.1=b j):finite b g p=p ↔ ∀i,i≠j→coordinate (F:=ℂ) i g=1:=by
  rw [finite_fixed_iff]
  have hz:p.val.2 j=0:=by
    have he:=p.property j
    rw [hp,sub_self] at he
    exact sq_eq_zero_iff.mp he
  have hn:∀i,i≠j→p.val.2 i≠0:=by
    intro i hij hi
    have he:=p.property i
    rw [hi,zero_pow (by decide:2≠0),hp] at he
    exact hij (hb (sub_eq_zero.mp he.symm).symm)
  constructor
  · intro h i hij
    exact h i (hn i hij)
  · intro h i hi
    exact h i (by intro he;subst i;exact hi hz)

lemma infinity_fixed_iff (g:FourBinaryCharacters318.Group) (s:InfinitySigns):
    signs g s=s ↔ ∀i,coordinate (F:=ℂ) i g=coordinate (F:=ℂ) 0 g:=by
  have hs:∀i,s.val i≠0:=by
    intro i hi
    have he:=s.property.2 i
    rw [hi,zero_pow (by decide:2≠0)] at he
    exact zero_ne_one he
  constructor
  · intro h i
    have he:=congrArg (fun q:InfinitySigns=>q.val i) h
    change (coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g)*s.val i=s.val i at he
    have hc:coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g=1:=
      mul_right_cancel₀ (hs i) (by simpa using he)
    have hh:=congrArg (fun z:ℂ=>z*coordinate (F:=ℂ) 0 g) hc
    simpa only [mul_assoc,←pow_two,coordinate_square,mul_one,one_mul] using hh
  · intro h
    apply Subtype.ext
    funext i
    change coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g*s.val i=s.val i
    rw [h i,←pow_two,coordinate_square,one_mul]

/-- The coordinate-ring maps obey the SAME full group law. -/
lemma finiteEnd_mul (g h:FourBinaryCharacters318.Group):
    FourRootCoordinateRingSigns318.finiteEnd b (g*h)=
      (FourRootCoordinateRingSigns318.finiteEnd b g).comp
        (FourRootCoordinateRingSigns318.finiteEnd b h):=by
  apply FourRootAffineCoordinateRing318.hom_ext
  intro k
  cases k with
  | none=>simp only [AlgHom.comp_apply,FourRootCoordinateRingSigns318.finite_base]
  | some i=>
    simp only [AlgHom.comp_apply,FourRootCoordinateRingSigns318.finite_root,
      map_mul,AlgHom.commutes]
    ring

lemma infinityEnd_mul (g h:FourBinaryCharacters318.Group):
    FourRootCoordinateRingSigns318.infinityEnd b (g*h)=
      (FourRootCoordinateRingSigns318.infinityEnd b g).comp
        (FourRootCoordinateRingSigns318.infinityEnd b h):=by
  apply FourRootInfinityCoordinateRing318.hom_ext
  intro k
  cases k with
  | none=>
    simp only [AlgHom.comp_apply,FourRootCoordinateRingSigns318.infinity_parameter,
      map_mul,AlgHom.commutes]
    ring
  | some i=>
    simp only [AlgHom.comp_apply,FourRootCoordinateRingSigns318.infinity_ratio,
      map_mul,AlgHom.commutes]
    ring
end FourRootActionStabilizers318
