module
public import LegendreSquarefreeCRT318
public import TwoTwistPointRealization318
public section
noncomputable section
namespace ActualPreparedPoleSquarefreeClasses318

/-- A positive rational has a positive natural squarefree representative
with an explicit nonzero rational scale. This is ordinary rational arithmetic,
not a local-to-global statement about elliptic points. -/
theorem positive_squarefree (x : ℚ) (hx : 0<x) :
    ∃ a : ℕ, ∃ r : ℚ, 0<a ∧ Squarefree a ∧ r≠0 ∧ x=(a:ℚ)*r^2 := by
  have hden : (x.den:ℚ)≠0 := by exact_mod_cast x.den_ne_zero
  have hdenpos : (0:ℚ)<x.den := by exact_mod_cast x.den_pos
  have hnum : (x.num:ℚ)=x*(x.den:ℚ) := by
    calc
      (x.num:ℚ)=((x.num:ℚ)/(x.den:ℚ))*(x.den:ℚ) := by field_simp [hden]
      _=x*(x.den:ℚ) := by rw [Rat.num_div_den]
  have hnumposQ : (0:ℚ)<x.num := by rw [hnum]; exact mul_pos hx hdenpos
  have hnumpos : (0:ℤ)<x.num := by exact_mod_cast hnumposQ
  have hnpos : (0:ℤ)<x.num*(x.den:ℤ) := mul_pos hnumpos (by exact_mod_cast x.den_pos)
  obtain ⟨e,d,he0,hd0,he,hsf,_⟩ :=
    LegendreSquarefreeCRT318.normalize (x.num*(x.den:ℤ)) (ne_of_gt hnpos)
  have hdpos : (0:ℤ)<d := by
    have hprod : (0:ℤ)<e^2*d := by rw [he]; exact hnpos
    exact (mul_pos_iff_of_pos_left (sq_pos_of_ne_zero he0)).mp hprod
  have hdcast : (d.natAbs:ℤ)=d := by
    rw [Int.natCast_natAbs,abs_of_pos hdpos]
  have hdcastQ : (d.natAbs:ℚ)=(d:ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hdcast
  have heQ : (e:ℚ)≠0 := by exact_mod_cast he0
  have heq : (e:ℚ)^2*(d:ℚ)=(x.num:ℚ)*(x.den:ℚ) := by exact_mod_cast he
  refine ⟨d.natAbs,(e:ℚ)/(x.den:ℚ),Int.natAbs_pos.mpr hd0,
    Int.squarefree_natAbs.mpr hsf,div_ne_zero heQ hden,?_⟩
  rw [hdcastQ]
  calc
    x=(x.num:ℚ)/(x.den:ℚ) := (Rat.num_div_den x).symm
    _=((x.num:ℚ)*(x.den:ℚ))/(x.den:ℚ)^2 := by field_simp [hden]
    _=((e:ℚ)^2*(d:ℚ))/(x.den:ℚ)^2 := by rw [heq]
    _=(d:ℚ)*((e:ℚ)/(x.den:ℚ))^2 := by ring

/-- Literal positive squarefree representatives of the TWO actual class
quantities at the fixed pole b. Residues and mutual local squares are separate
conclusions to be derived from actual preparation, not assumed here. -/
structure Classes (b : ℚ) where
  beta : ℕ
  theta : ℕ
  beta_pos : 0<beta
  theta_pos : 0<theta
  beta_squarefree : Squarefree beta
  theta_squarefree : Squarefree theta
  c : ℚ
  d : ℚ
  c_ne : c≠0
  d_ne : d≠0
  first_class : 17*b=(beta:ℚ)*c^2
  second_class : (17*b)^2*(1-b/17)=(theta:ℚ)*d^2

/-- The same actual b supplies its squarefree classes; no alternative pole
or independently chosen source index is substituted. -/
theorem classes_exist (b : ℚ) (hb : 0<b) (hsmall : b<17) : Nonempty (Classes b) := by
  have hB : (0:ℚ)<17*b := by positivity
  have htheta : (0:ℚ)<1-b/17 := by linarith
  have hV : (0:ℚ)<(17*b)^2*(1-b/17) := mul_pos (sq_pos_of_pos hB) htheta
  obtain ⟨beta,c,hbeta,hsbeta,hc,hBfactor⟩ := positive_squarefree (17*b) hB
  obtain ⟨theta,d,htheta',hstheta,hd,hVfactor⟩ :=
    positive_squarefree ((17*b)^2*(1-b/17)) hV
  exact ⟨⟨beta,theta,hbeta,htheta',hsbeta,hstheta,c,d,hc,hd,hBfactor,hVfactor⟩⟩

/-- Once the genuine two rational point producers are available, these
actual classes plug into the existing Realization without a new matching premise. -/
def Classes.realization {b : ℚ} (C : Classes b) (n : ℚ)
    (P : TwoTwistPointRealization318.SquareclassPoint (C.beta:ℚ) n)
    (Q : TwoTwistPointRealization318.SquareclassPoint (C.beta:ℚ) (n*(C.theta:ℚ))) :
    TwoTwistPointRealization318.Realization b where
  β := C.beta
  θ := C.theta
  c := C.c
  d := C.d
  n := n
  c_ne := C.c_ne
  d_ne := C.d_ne
  first_class := C.first_class
  second_class := C.second_class
  first := P
  second := Q

end ActualPreparedPoleSquarefreeClasses318
