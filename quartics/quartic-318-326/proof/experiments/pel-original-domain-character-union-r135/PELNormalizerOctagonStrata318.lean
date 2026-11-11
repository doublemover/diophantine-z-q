module
public import PELNormalizerOctagonImageCertificate318
public import FiniteStrictRadialExtension318
public section
namespace PELNormalizerOctagonStrata318
open PELNormalizerOctagonAffine318 PELNormalizerOctagonVertices318
open PELNormalizerOctagonImageCertificate318
set_option maxHeartbeats 3000000
@[expose] def strict (P : ℝ × ℝ) : Prop :=
  -1<P.2 ∧ P.2<1 ∧ -30<P.1 ∧ P.1<30 ∧
    -35<P.1+7*P.2 ∧ P.1+7*P.2<35 ∧ -35<P.1-7*P.2 ∧ P.1-7*P.2<35
@[expose] def mix (v : Fin 8) (s : ℝ) : ℝ × ℝ :=
  ((1-s)*((vertex v).1:ℝ)+s*((vertex (next v)).1:ℝ),
   (1-s)*((vertex v).2:ℝ)+s*((vertex (next v)).2:ℝ))

/-- Actual full point stratification of the closed octagon. Every
non-strict point lies on one literal whole closed side, endpoints included. -/
theorem closed_side_or_strict (P : ℝ × ℝ) (hP : inequalities P.1 P.2) :
    strict P ∨ ∃ v : Fin 8,∃ s : ℝ,0≤s ∧ s≤1 ∧ P=mix v s := by
  obtain ⟨hb0,hb1,ha0,ha1,hs0,hs1,ht0,ht1⟩ := hP
  by_cases h0 : P.2=1
  · right; refine ⟨0,(28-P.1)/56,?_,?_,?_⟩
    · linarith
    · linarith
    · ext <;> norm_num [mix,vertex,next] <;> linarith
  by_cases h1 : P.1-7*P.2=-35
  · right; refine ⟨1,(-28-P.1)/2,?_,?_,?_⟩
    · linarith
    · linarith
    · ext <;> norm_num [mix,vertex,next] <;> linarith
  by_cases h2 : P.1=-30
  · right; refine ⟨2,(5-7*P.2)/10,?_,?_,?_⟩
    · linarith
    · linarith
    · ext <;> norm_num [mix,vertex,next] <;> linarith
  by_cases h3 : P.1+7*P.2=-35
  · right; refine ⟨3,(P.1+30)/2,?_,?_,?_⟩
    · linarith
    · linarith
    · ext <;> norm_num [mix,vertex,next] <;> linarith
  by_cases h4 : P.2=-1
  · right; refine ⟨4,(P.1+28)/56,?_,?_,?_⟩
    · linarith
    · linarith
    · ext <;> norm_num [mix,vertex,next] <;> linarith
  by_cases h5 : P.1-7*P.2=35
  · right; refine ⟨5,(P.1-28)/2,?_,?_,?_⟩
    · linarith
    · linarith
    · ext <;> norm_num [mix,vertex,next] <;> linarith
  by_cases h6 : P.1=30
  · right; refine ⟨6,(7*P.2+5)/10,?_,?_,?_⟩
    · linarith
    · linarith
    · ext <;> norm_num [mix,vertex,next] <;> linarith
  by_cases h7 : P.1+7*P.2=35
  · right; refine ⟨7,(30-P.1)/2,?_,?_,?_⟩
    · linarith
    · linarith
    · ext <;> norm_num [mix,vertex,next] <;> linarith
  left
  exact ⟨lt_of_le_of_ne hb0 h4.symm,lt_of_le_of_ne hb1 h0,
    lt_of_le_of_ne ha0 h2.symm,lt_of_le_of_ne ha1 h6,
    lt_of_le_of_ne hs0 h3.symm,lt_of_le_of_ne hs1 h7,
    lt_of_le_of_ne ht0 h1.symm,lt_of_le_of_ne ht1 h5⟩
end PELNormalizerOctagonStrata318
