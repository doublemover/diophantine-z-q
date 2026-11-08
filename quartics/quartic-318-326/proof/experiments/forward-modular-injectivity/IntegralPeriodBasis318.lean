module
public import ScaledPeriodLattice318
public import ModularLattice318
public section
noncomputable section
open scoped MatrixGroups
namespace IntegralPeriodBasis318
open PeriodEisenstein318
set_option maxHeartbeats 0

lemma coefficients_unique (tau : UpperHalfPlane) (m n p q : ℤ)
    (he : (m:ℂ)*tau+n=(p:ℂ)*tau+q) : m=p ∧ n=q := by
  have hi := congrArg Complex.im he
  simp only [Complex.add_im,Complex.mul_im,Complex.intCast_re,Complex.intCast_im,
    zero_mul,add_zero] at hi
  have hm : m=p := by exact_mod_cast mul_right_cancel₀ tau.im_pos.ne' hi
  refine ⟨hm,?_⟩
  rw [hm] at he
  exact_mod_cast add_left_cancel he

lemma determinant_positive (tau sigma : UpperHalfPlane) (u : ℂˣ) (a b c d : ℤ)
    (ha : (a:ℂ)*tau+b=(u:ℂ)*sigma) (hc : (c:ℂ)*tau+d=(u:ℂ)) :
    0<a*d-b*c := by
  have hi : ‖(u:ℂ)‖^2*sigma.im=((a*d-b*c:ℤ):ℝ)*tau.im := by
    calc
      ‖(u:ℂ)‖^2*sigma.im=(((u:ℂ)*sigma)*star (u:ℂ)).im := by
        rw [mul_right_comm,Complex.mul_conj']
        simp
      _=(((a:ℂ)*tau+b)*star ((c:ℂ)*tau+d)).im := by rw [←ha,←hc]
      _=((a*d-b*c:ℤ):ℝ)*tau.im := by
        simp only [Complex.mul_im,Complex.mul_re,Complex.add_im,Complex.add_re,
          Complex.intCast_re,Complex.intCast_im,Complex.conj_im,Complex.conj_re,
          Int.cast_sub,Int.cast_mul]
        ring
  have hp : 0<‖(u:ℂ)‖^2*sigma.im :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (Units.ne_zero u))) sigma.im_pos
  have hd : 0<((a*d-b*c:ℤ):ℝ) := by nlinarith [tau.im_pos]
  exact_mod_cast hd

/-- Homothety of the literal period lattices determines an actual orientation-preserving
integral change of basis, including its exact denominator. -/
theorem exists_modular_matrix (tau sigma : UpperHalfPlane) (u : ℂˣ)
    (H : ∀ z : ℂ, z∈(periods tau).lattice ↔ (u:ℂ)⁻¹*z∈(periods sigma).lattice) :
    ∃ g : SL(2,ℤ), g•tau=sigma ∧ ModularLattice318.d g tau=(u:ℂ) := by
  have hsigma : (sigma:ℂ)∈(periods sigma).lattice := by
    exact PeriodPair.mem_lattice.mpr ⟨1,0,by simp [periods]⟩
  have honeS : (1:ℂ)∈(periods sigma).lattice := by
    exact PeriodPair.mem_lattice.mpr ⟨0,1,by simp [periods]⟩
  have htau : (tau:ℂ)∈(periods tau).lattice := by
    exact PeriodPair.mem_lattice.mpr ⟨1,0,by simp [periods]⟩
  have honeT : (1:ℂ)∈(periods tau).lattice := by
    exact PeriodPair.mem_lattice.mpr ⟨0,1,by simp [periods]⟩
  have huS : (u:ℂ)*sigma∈(periods tau).lattice := (H _).mpr (by simpa using hsigma)
  have hu1 : (u:ℂ)∈(periods tau).lattice := (H _).mpr (by simpa using honeS)
  obtain ⟨a,b,ha⟩ := PeriodPair.mem_lattice.mp huS
  obtain ⟨c,d,hc⟩ := PeriodPair.mem_lattice.mp hu1
  obtain ⟨e,f,he⟩ := PeriodPair.mem_lattice.mp ((H _).mp htau)
  obtain ⟨g,h,hg⟩ := PeriodPair.mem_lattice.mp ((H _).mp honeT)
  simp only [periods,mul_one] at ha hc he hg
  have hfirst : (((e*a+f*c:ℤ):ℂ)*tau+(e*b+f*d:ℤ))=(1:ℂ)*tau+(0:ℂ) := by
    push_cast
    calc
      _=(e:ℂ)*((a:ℂ)*tau+b)+(f:ℂ)*((c:ℂ)*tau+d) := by ring
      _=(u:ℂ)*((e:ℂ)*sigma+f) := by rw [ha,hc]; ring
      _=_ := by rw [he]; field_simp
  have hsecond : (((g*a+h*c:ℤ):ℂ)*tau+(g*b+h*d:ℤ))=(0:ℂ)*tau+(1:ℂ) := by
    push_cast
    calc
      _=(g:ℂ)*((a:ℂ)*tau+b)+(h:ℂ)*((c:ℂ)*tau+d) := by ring
      _=(u:ℂ)*((g:ℂ)*sigma+h) := by rw [ha,hc]; ring
      _=_ := by rw [hg]; field_simp
  have h1 := coefficients_unique tau (e*a+f*c) (e*b+f*d) 1 0 hfirst
  have h2 := coefficients_unique tau (g*a+h*c) (g*b+h*d) 0 1 hsecond
  have hdet : (e*h-f*g)*(a*d-b*c)=1 := by
    calc
      _=(e*a+f*c)*(g*b+h*d)-(e*b+f*d)*(g*a+h*c) := by ring
      _=1 := by rw [h1.1,h1.2,h2.1,h2.2]; norm_num
  have hunit : IsUnit (a*d-b*c) := IsUnit.of_mul_eq_one_right _ hdet
  have hpositive := determinant_positive tau sigma u a b c d ha hc
  have hdet1 : a*d-b*c=1 := by
    rcases Int.isUnit_eq_one_or hunit with hd | hd
    · exact hd
    · omega
  let G : SL(2,ℤ) := ⟨!![a,b;c,d],by simpa [Matrix.det_fin_two] using hdet1⟩
  have hden : ModularLattice318.d G tau=(u:ℂ) := by simpa [G,ModularLattice318.d] using hc
  refine ⟨G,?_,hden⟩
  apply UpperHalfPlane.coe_injective
  rw [ModularLattice318.action_formula,hden]
  change ((a:ℂ)*tau+b)/(u:ℂ)=(sigma:ℂ)
  rw [ha]
  field_simp

end IntegralPeriodBasis318
