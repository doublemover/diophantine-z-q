module
public import Mathlib.Tactic
public section
namespace ActualTorsorIntegralCertificates318
set_option maxHeartbeats 1000000
variable {S : Type*} [CommRing S]
abbrev V (S : Type*) := Fin 3 → S

@[expose] def den : Fin 2 → ℕ := ![705600,246960]
@[expose] def detV (p : V S) := p 0*p 2-(p 1)^2
@[expose] def fV (i : Fin 2) (p : V S) :=
  ![-43*(p 0)^2+2*p 0*p 1+505*p 0*p 2+12*p 1*p 2-1548*(p 2)^2,
    -43*(p 0)^2+256*p 0*p 1-130*p 0*p 2-768*p 1*p 2-387*(p 2)^2] i
@[expose] def nV (i : Fin 2) (p : V S) :=
  -10976 * ![(p 0)^2-14*p 0*p 1+65*p 0*p 2-84*p 1*p 2+36*(p 2)^2,
    (p 0+4*p 1-3*p 2)^2] i
@[expose] def enc (i : Fin 2) (p : V S) : V S :=
  ![![240*p 0-1920*p 1+1440*p 2,11760*p 0-70560*p 2,735*p 0-2205*p 1+4410*p 2],
    ![392*p 0+1568*p 1-1176*p 2,11760*p 0-35280*p 1-35280*p 2,735*p 0+2205*p 2]] i
@[expose] def num (i : Fin 2) (r : V S) : V S :=
  ![![-882*r 0+30*r 1+768*r 2,-588*r 0+192*r 2,-147*r 0-5*r 1+128*r 2],
    ![135*r 0+6*r 1+168*r 2,90*r 0-3*r 1,-45*r 0-2*r 1+56*r 2]] i
@[expose] def rad (i : Fin 2) (t : S) : V S :=
  ![![-6*(t-32),42*(t-76832),-21*(t+343)],![-14*t,42*(t-76832),-21*(t+343)]] i
@[expose] def scale (h : S) (p : V S) : V S := fun j => h*p j
@[expose] def dec (i : Fin 2) (h : S) (r : V S) := scale h (num i r)

theorem enc_num (i : Fin 2) (p : V S) (j : Fin 3) : enc i (num i p) j=(den i:S)*p j := by
  fin_cases i <;> fin_cases j <;> norm_num [enc,num,den] <;> ring
theorem num_enc (i : Fin 2) (p : V S) (j : Fin 3) : num i (enc i p) j=(den i:S)*p j := by
  fin_cases i <;> fin_cases j <;> norm_num [enc,num,den] <;> ring
theorem enc_scale (i : Fin 2) (h : S) (p : V S) (j : Fin 3) : enc i (scale h p) j=h*enc i p j := by
  fin_cases i <;> fin_cases j <;> norm_num [enc,scale] <;> ring
theorem enc_dec (i : Fin 2) (h : S) (hd : h*(den i:S)=1) (p : V S) (j : Fin 3) :
    enc i (dec i h p) j=p j := by rw [dec,enc_scale,enc_num,←mul_assoc,hd,one_mul]
theorem dec_enc (i : Fin 2) (h : S) (hd : h*(den i:S)=1) (p : V S) (j : Fin 3) :
    dec i h (enc i p) j=p j := by
  change h*num i (enc i p) j=p j
  rw [num_enc,←mul_assoc,hd,one_mul]

theorem forms_scale (i : Fin 2) (h : S) (p : V S) :
    detV (scale h p)=h^2*detV p ∧ fV i (scale h p)=h^2*fV i p ∧
      nV i (scale h p)=h^2*nV i p := by
  refine ⟨?_,?_,?_⟩ <;> fin_cases i <;> norm_num [scale,detV,fV,nV] <;> ring

/-- Integer certificates for the full ideal, valid on nilpotents and
in every residue characteristic; not just equalities of geometric roots. -/
theorem ver_to_rad (i : Fin 2) (t : S) (p : V S)
    (hd : detV p=0) (hf : fV i p=1) (hn : nV i p=t) (j : Fin 3) :
    (enc i p j)^2=rad i t j := by
  fin_cases i <;> fin_cases j <;> norm_num [detV,fV,nV,rad,enc] at hd hf hn ⊢
  · linear_combination -3686400*hd-6*hn+192*hf
  · linear_combination 42*hn-3226944*hf
  · linear_combination -4862025*hd-21*hn-7203*hf
  · linear_combination -14*hn
  · linear_combination -1252054272*hd+42*hn-3226944*hf
  · linear_combination 3687936*hd-21*hn-7203*hf

theorem rad_to_num (i : Fin 2) (t : S) (r : V S) (h : ∀ j, (r j)^2=rad i t j) :
    detV (num i r)=0 ∧ fV i (num i r)=(den i:S)^2 ∧
      nV i (num i r)=(den i:S)^2*t := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  fin_cases i <;> norm_num [num,rad,detV,fV,nV,den] at h0 h1 h2 ⊢
  · refine ⟨?_,?_,?_⟩
    · linear_combination -216090*h0-150*h1+61440*h2
    · linear_combination 648270*h0-153150*h1-491520*h2
    · linear_combination 49807880640*h0+87259200*h1-37764464640*h2
  · refine ⟨?_,?_,?_⟩
    · linear_combination -14175*h0-21*h1+9408*h2
    · linear_combination 5443200*h0-10752*h1-3650304*h2
    · linear_combination -4356374400*h0

theorem rad_to_ver (i : Fin 2) (t h : S) (hh : h*(den i:S)=1) (r : V S)
    (hr : ∀ j, (r j)^2=rad i t j) :
    detV (dec i h r)=0 ∧ fV i (dec i h r)=1 ∧ nV i (dec i h r)=t := by
  obtain ⟨d,f,n⟩ := rad_to_num i t r hr
  obtain ⟨sd,sf,sn⟩ := forms_scale i h (num i r)
  have hs : h^2*(den i:S)^2=1 := by rw [←mul_pow,hh,one_pow]
  exact ⟨sd.trans (by rw [d,mul_zero]),sf.trans (by rw [f,hs]),
    sn.trans (by rw [n,←mul_assoc,hs,one_mul])⟩

variable {T : Type*} [CommRing T]
theorem map_enc (g : S →+* T) (i : Fin 2) (p : V S) (j : Fin 3) :
    g (enc i p j)=enc i (fun k => g (p k)) j := by
  fin_cases i <;> fin_cases j <;> simp [enc,map_ofNat]
theorem map_num (g : S →+* T) (i : Fin 2) (p : V S) (j : Fin 3) :
    g (num i p j)=num i (fun k => g (p k)) j := by
  fin_cases i <;> fin_cases j <;> simp [num,map_ofNat]
theorem map_rad (g : S →+* T) (i : Fin 2) (t : S) (j : Fin 3) :
    g (rad i t j)=rad i (g t) j := by fin_cases i <;> fin_cases j <;> simp [rad,map_ofNat]
theorem map_forms (g : S →+* T) (i : Fin 2) (p : V S) :
    g (detV p)=detV (fun k=>g (p k)) ∧ g (fV i p)=fV i (fun k=>g (p k)) ∧
    g (nV i p)=nV i (fun k=>g (p k)) := by
  refine ⟨?_,?_,?_⟩ <;> fin_cases i <;> simp [detV,fV,nV,map_ofNat]

end ActualTorsorIntegralCertificates318
