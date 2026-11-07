module
public import FormalStabilizer318
public import Mathlib.GroupTheory.GroupAction.Quotient
public section
noncomputable section
namespace FiveBranchCount318
attribute [local instance] Classical.propDecidable
open MulAction
set_option maxHeartbeats 0
variable {G Ω k:Type*} [Group G] [Fintype G] [Fintype Ω] [MulAction G Ω] [Field k]

/-- A point in the ramification locus has a nontrivial stabilizer. Combined
with the actual tame formal-coordinate action this forces its order to be2. -/
theorem stabilizer_card_two (hchar:(2:k)≠0) (hperiod:∀g:G,g*g=1)
    (A:∀x:Ω,FormalStabilizer318.Action (stabilizer G x) k)
    (hbranch:∀x:Ω,∃g:G,g≠1 ∧ g•x=x) (x:Ω) :
    Nat.card (stabilizer G x)=2 := by
  classical
  letI:Fintype (stabilizer G x):=Fintype.ofFinite _
  have hu:Fintype.card (stabilizer G x)≤2:= (A x).card_le_two hchar (by
    intro g
    apply Subtype.ext
    exact hperiod g.val)
  obtain ⟨g,hg,hfix⟩:=hbranch x
  have hgmem:g∈stabilizer G x:=hfix
  have hn:Nontrivial (stabilizer G x):=⟨⟨⟨g,hgmem⟩,1,by
    intro he
    exact hg (congrArg Subtype.val he)⟩⟩
  have hl:1<Fintype.card (stabilizer G x):=Fintype.one_lt_card_iff_nontrivial.mpr hn
  rw [Nat.card_eq_fintype_card]
  omega

theorem branch_orbit_card_eight (hG:Fintype.card G=16)
    (hchar:(2:k)≠0) (hperiod:∀g:G,g*g=1)
    (A:∀x:Ω,FormalStabilizer318.Action (stabilizer G x) k)
    (hbranch:∀x:Ω,∃g:G,g≠1 ∧ g•x=x) (x:Ω) :
    Nat.card (orbit G x)=8 := by
  classical
  letI:Fintype (stabilizer G x):=Fintype.ofFinite _
  letI:Fintype (orbit G x):=Fintype.ofFinite _
  have hs:=stabilizer_card_two hchar hperiod A hbranch x
  rw [Nat.card_eq_fintype_card] at hs ⊢
  have ho:=MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
  rw [hs,hG] at ho
  omega

/-- Actual orbit decomposition, rather than an assumed number of branch values. -/
theorem five_orbits (hG:Fintype.card G=16) (hΩ:Fintype.card Ω=40)
    (hchar:(2:k)≠0) (hperiod:∀g:G,g*g=1)
    (A:∀x:Ω,FormalStabilizer318.Action (stabilizer G x) k)
    (hbranch:∀x:Ω,∃g:G,g≠1 ∧ g•x=x) :
    Nat.card (Quotient (MulAction.orbitRel G Ω))=5 := by
  classical
  letI:Fintype (Quotient (MulAction.orbitRel G Ω)):=Fintype.ofFinite _
  letI:(x:Ω)→Fintype (orbit G x):=fun _=>Fintype.ofFinite _
  have he:=Fintype.card_congr (MulAction.selfEquivSigmaOrbits G Ω)
  rw [Fintype.card_sigma] at he
  have ho:∀x:Ω,Fintype.card (orbit G x)=8:=by
    intro x
    simpa only [Nat.card_eq_fintype_card] using branch_orbit_card_eight hG hchar hperiod A hbranch x
  simp_rw [ho] at he
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at he
  rw [hΩ] at he
  rw [Nat.card_eq_fintype_card]
  change 40=Fintype.card (Quotient (MulAction.orbitRel G Ω))*8 at he
  omega

/-- Two distinct nonidentity involutions cannot fix the same formal-smooth point. -/
theorem unique_nontrivial_fixer (hchar:(2:k)≠0) (hperiod:∀g:G,g*g=1)
    (A:∀x:Ω,FormalStabilizer318.Action (stabilizer G x) k)
    (x:Ω) (g h:G) (hg:g≠1) (hh:h≠1) (hgf:g•x=x) (hhf:h•x=x) : g=h := by
  let g':stabilizer G x:=⟨g,hgf⟩
  let h':stabilizer G x:=⟨h,hhf⟩
  have hp:∀a:stabilizer G x,a*a=1:=by
    intro a
    apply Subtype.ext
    exact hperiod a.val
  have hgt:(A x).tangent g'= -1:=by
    rcases (A x).tangent_sign hp g' with ht|ht
    · have he: g'=1 := (A x).eq_one_of_tangent_one hchar g' (hp g') ht
      exact False.elim (hg (congrArg Subtype.val he))
    · exact ht
  have hht:(A x).tangent h'= -1:=by
    rcases (A x).tangent_sign hp h' with ht|ht
    · have he: h'=1 := (A x).eq_one_of_tangent_one hchar h' (hp h') ht
      exact False.elim (hh (congrArg Subtype.val he))
    · exact ht
  exact congrArg Subtype.val ((A x).tangent_injective hchar hp (hgt.trans hht.symm))

/-- Actual nonidentity fixed-point incidence count equals the size of the
ramification locus; no overlap between involution fixed loci is assumed. -/
theorem nonidentity_fixed_sum (hchar:(2:k)≠0) (hperiod:∀g:G,g*g=1)
    (A:∀x:Ω,FormalStabilizer318.Action (stabilizer G x) k)
    (hbranch:∀x:Ω,∃g:G,g≠1 ∧ g•x=x) :
    (∑g:{g:G // g≠1},Nat.card (fixedBy Ω g.val))=Fintype.card Ω := by
  classical
  let T:=Σg:{g:G // g≠1},fixedBy Ω g.val
  let f:T→Ω:=fun a=>a.2.val
  have hi:Function.Injective f:=by
    rintro ⟨⟨g,hg⟩,⟨x,hx⟩⟩ ⟨⟨h,hh⟩,⟨y,hy⟩⟩ he
    change x=y at he
    subst y
    have hgh:g=h:=unique_nontrivial_fixer hchar hperiod A x g h hg hh hx hy
    subst h
    rfl
  have hs:Function.Surjective f:=by
    intro x
    obtain ⟨g,hg,hfix⟩:=hbranch x
    exact ⟨⟨⟨g,hg⟩,⟨x,hfix⟩⟩,rfl⟩
  letI:(g:{g:G // g≠1})→Fintype (fixedBy Ω g.val):=fun _=>Fintype.ofFinite _
  have hc:=Fintype.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)
  change Fintype.card (Σg:{g:G // g≠1},fixedBy Ω g.val)=_ at hc
  rw [Fintype.card_sigma] at hc
  simpa only [Nat.card_eq_fintype_card] using hc

/-- Four actual distinct8-point fixed loci supply the32-point lower bound. -/
theorem four_fixed_loci_lower (hchar:(2:k)≠0) (hperiod:∀g:G,g*g=1)
    (A:∀x:Ω,FormalStabilizer318.Action (stabilizer G x) k)
    (w:Fin 4→G) (hw:Function.Injective w) (hw1:∀i,w i≠1)
    (f:Fin 4→Fin 8→Ω) (hf:∀i,Function.Injective (f i))
    (hfix:∀i j,w i•f i j=f i j) : 32≤Fintype.card Ω := by
  let F:Fin 4×Fin 8→Ω:=fun a=>f a.1 a.2
  have hi:Function.Injective F:=by
    rintro ⟨i,j⟩ ⟨i',j'⟩ he
    change f i j=f i' j' at he
    have hwi:w i=w i':=unique_nontrivial_fixer hchar hperiod A (f i j)
      (w i) (w i') (hw1 i) (hw1 i') (hfix i j) (by rw [he];exact hfix i' j')
    have hii:i=i':=hw hwi
    subst i'
    have hjj:j=j':=hf i he
    subst j'
    rfl
  simpa using Fintype.card_le_of_injective F hi

/-- Genus5, degree16 Riemann--Hurwitz with the four known8-point fixed loci
forces quotient genus0 and total nontrivial fixed-point count40. -/
theorem source_riemann_hurwitz (g S:ℕ)
    (hRH:(8:ℤ)=16*(2*(g:ℤ)-2)+(S:ℤ)) (hknown:32≤S) :
    g=0 ∧ S=40 := by omega

/-- Source-specific finite group-action/Riemann--Hurwitz assembly. The actual
Riemann--Hurwitz identity and four quotient fixed loci are geometric inputs;
all incidence, stabilizer and orbit counts are derived. -/
theorem actual_five_branch_values (hG:Fintype.card G=16)
    (hchar:(2:k)≠0) (hperiod:∀g:G,g*g=1)
    (A:∀x:Ω,FormalStabilizer318.Action (stabilizer G x) k)
    (hbranch:∀x:Ω,∃g:G,g≠1 ∧ g•x=x)
    (w:Fin 4→G) (hw:Function.Injective w) (hw1:∀i,w i≠1)
    (f:Fin 4→Fin 8→Ω) (hf:∀i,Function.Injective (f i))
    (hfix:∀i j,w i•f i j=f i j) (genus:ℕ)
    (hRH:(8:ℤ)=16*(2*(genus:ℤ)-2)+
      ((∑g:{g:G // g≠1},Nat.card (fixedBy Ω g.val)):ℕ)) :
    genus=0 ∧ Fintype.card Ω=40 ∧ Nat.card (Quotient (orbitRel G Ω))=5 := by
  have hs:=nonidentity_fixed_sum hchar hperiod A hbranch
  rw [hs] at hRH
  have hl:=four_fixed_loci_lower hchar hperiod A w hw hw1 f hf hfix
  obtain ⟨hg,hΩ⟩:=source_riemann_hurwitz genus (Fintype.card Ω) hRH hl
  exact ⟨hg,hΩ,five_orbits hG hΩ hchar hperiod A hbranch⟩

end FiveBranchCount318
