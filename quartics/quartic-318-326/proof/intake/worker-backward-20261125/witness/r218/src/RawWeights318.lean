module
public import RawDetector318
public import LocalSoundness318
public import DegenerateDetector
public section
namespace RawWeights318
open CircuitReplay Raw318FinalReplay
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

/-! Actual final source weights. All CSE normalizations and fused base rows
are decoded, including the A-dependent contact order R=v(F)-5v(A). -/
@[expose] def contactPolynomial (t : ℚ) : ℚ :=
  t*(t+1/2)*(t+1)*(t-1/2399)*(t+32/407)
@[expose] def t0 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 38))
@[expose] def F0 (S : ℚ) (w : Assignment) : ℚ := ((76265 / 1952786 : ℚ) * (w 147) + (3081901 / 1952786 : ℚ) * (w 149) + (-16 / 976393 : ℚ) * (w 38))
@[expose] def e0 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 1 : ℚ) * (w 151) + (-1 / 1 : ℚ) * (w 152))
@[expose] def q0 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 151))
@[expose] def ed0 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 151) + (1 / 1 : ℚ) * (w 152) + (-1 / 1 : ℚ) * (w 153))
@[expose] def aa0 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 154))
@[expose] def cc0 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 155))
@[expose] def xx0 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 156))
@[expose] def yy0 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 157))
@[expose] def zz0 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 158))
@[expose] def ad0 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 1 : ℚ) + (1 / 1 : ℚ) * (w 38))
@[expose] def delta0 (S : ℚ) (w : Assignment) : ℚ := t0 S w-1
@[expose] def A0 (S : ℚ) (w : Assignment) : ℚ := (1 : ℚ)

theorem F0_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    F0 S w=contactPolynomial (t0 S w) := by
  have hr110 : r110 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=110) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg149 : w 149=((1 / 1 : ℚ) * (w 147) * (w 147) + (1952786 / 3081901 : ℚ) * (w 147) * (w 148) + (1205412 / 3081901 : ℚ) * (w 38) * (w 147)) := by dsimp only [r110] at hr110; linear_combination hr110
  have hr109 : r109 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=109) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg148 : w 148=((1 / 1 : ℚ) * (w 38) * (w 147)) := by dsimp only [r109] at hr109; linear_combination hr109
  have hr108 : r108 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=108) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg147 : w 147=((1 / 1 : ℚ) * (w 38) * (w 38)) := by dsimp only [r108] at hr108; linear_combination hr108
  dsimp only [F0,t0,contactPolynomial]
  rw [hg149,hg148,hg147]
  ring

theorem qd0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q0 S w*(delta0 S w)^3=e0 S w := by
  have hr111 : r111 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=111) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg150 : w 150=((1 / 1 : ℚ) * (w 38) * (w 147) + (-2 / 1 : ℚ) * (w 38) * (w 38)) := by dsimp only [r111] at hr111; linear_combination hr111
  have hr108 : r108 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=108) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg147 : w 147=((1 / 1 : ℚ) * (w 38) * (w 38)) := by dsimp only [r108] at hr108; linear_combination hr108
  have hr113 : r113 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=113) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [e0,q0,t0,delta0,t0]
  dsimp only [r113] at hr113
  simp only [hg150,hg147] at hr113 ⊢
  linear_combination (1 / 1 : ℚ)*hr113

theorem ed0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ed0 S w=e0 S w*delta0 S w := by
  have hr114 : r114 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=114) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [e0,ed0,t0,delta0,t0]
  dsimp only [r114] at hr114
  linear_combination (-1 / 1 : ℚ)*hr114

theorem aa0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    aa0 S w=(e0 S w)^2 := by
  have hr115 : r115 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=115) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [aa0,e0,delta0,t0]
  dsimp only [r115] at hr115
  linear_combination (1 / 1 : ℚ)*hr115

theorem cc0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    cc0 S w*delta0 S w=(aa0 S w)^2 := by
  have hr116 : r116 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=116) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [cc0,aa0,t0,delta0,t0]
  dsimp only [r116] at hr116
  linear_combination (1 / 1 : ℚ)*hr116

theorem xx0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    xx0 S w*ed0 S w=(cc0 S w)^2 := by
  have hr117 : r117 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=117) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [xx0,ed0,cc0,delta0,t0]
  dsimp only [r117] at hr117
  linear_combination (1 / 1 : ℚ)*hr117

theorem yy0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q0 S w*yy0 S w=(xx0 S w)^2 := by
  have hr118 : r118 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=118) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [q0,yy0,xx0,delta0,t0]
  dsimp only [r118] at hr118
  linear_combination (1 / 1 : ℚ)*hr118

theorem zz0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q0 S w*zz0 S w=(yy0 S w)^2 := by
  have hr119 : r119 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=119) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [q0,zz0,yy0,delta0,t0]
  dsimp only [r119] at hr119
  linear_combination (1 / 1 : ℚ)*hr119

theorem ad0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ad0 S w=A0 S w*delta0 S w := by simp [ad0,A0,delta0,t0]; ring

theorem eF0_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    e0 S w*F0 S w=(A0 S w*delta0 S w)^5 := by
  have hr108 : r108 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=108) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg147 : w 147=((1 / 1 : ℚ) * (w 38) * (w 38)) := by dsimp only [r108] at hr108; linear_combination hr108
  have hr112 : r112 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=112) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hqF : q0 S w*F0 S w=(delta0 S w)^2 := by
    dsimp only [q0,F0,delta0,t0]
    dsimp only [r112] at hr112
    simp only [hg147] at hr112 ⊢
    linear_combination hr112
  simpa only [A0,one_mul] using DegenerateDetector.base_fused_equation
    (q0 S w) (e0 S w) (delta0 S w) (F0 S w) (qd0_source S w source) hqF

theorem weight0_valuations (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (R : ℤ)
    (hve : v (e0 S w)=(-R:ℤ)) (hvd : v (delta0 S w)=0) :
    v (q0 S w)=(-R:ℤ) ∧ v (xx0 S w)=(-7*R:ℤ) ∧
      v (zz0 S w)=(-25*R:ℤ) ∧ v (ed0 S w)=(-R:ℤ) := by
  have he : e0 S w≠0 := (v.ne_top_iff).mp (by rw [hve]; simp)
  exact LocalSoundness318.weight_values v _ _ _ _ _ _ _ _ _ R he hve hvd
    (qd0_source S w source) (ed0_source S w source)
    (aa0_source S w source) (cc0_source S w source)
    (xx0_source S w source) (yy0_source S w source) (zz0_source S w source)

theorem contact0_valuations (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (a f : ℤ)
    (hA : v (A0 S w)=a) (hF : v (F0 S w)=f)
    (hd : v (delta0 S w)=0) (ha : Even a) (hf : Odd f) :
    Odd (f-5*a) ∧ v (q0 S w)=(-(f-5*a):ℤ) ∧
      v (xx0 S w)=(-7*(f-5*a):ℤ) ∧ v (zz0 S w)=(-25*(f-5*a):ℤ) ∧
      v (ed0 S w)=(-(f-5*a):ℤ) := by
  have he := LocalSoundness318.contact_e_value v _ _ _ _ a f hA hF hd
    (eF0_source S w source)
  have hve : v (e0 S w)=(-(f-5*a):ℤ) := by simpa only [show 5*a-f=-(f-5*a) by ring] using he
  exact ⟨LocalSoundness318.contact_R_odd f a hf ha,
    weight0_valuations S w source v (f-5*a) hve hd⟩

@[expose] def t1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 194))
@[expose] def F1 (S : ℚ) (w : Assignment) : ℚ := ((-16 / 976393 : ℚ) * (w 194) + (76265 / 1952786 : ℚ) * (w 195) + (602706 / 976393 : ℚ) * (w 197))
@[expose] def e1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 201))
@[expose] def q1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 203))
@[expose] def ed1 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 1 : ℚ) * (w 201) + (1 / 1 : ℚ) * (w 204))
@[expose] def aa1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 205))
@[expose] def cc1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 206))
@[expose] def xx1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 207))
@[expose] def yy1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 208))
@[expose] def zz1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 209))
@[expose] def ad1 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 1 : ℚ) * (w 198))
@[expose] def delta1 (S : ℚ) (w : Assignment) : ℚ := t1 S w-1
@[expose] def A1 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 143) * (w 143) + (2 / 1 : ℚ) * (w 143) * (w 145) + (1 / 1 : ℚ) * (w 145) * (w 145))

theorem F1_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    F1 S w=contactPolynomial (t1 S w) := by
  have hr160 : r160 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=160) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg197 : w 197=((1 / 1 : ℚ) * (w 194) * (w 195) + (3081901 / 1205412 : ℚ) * (w 195) * (w 195) + (976393 / 602706 : ℚ) * (w 195) * (w 196)) := by dsimp only [r160] at hr160; linear_combination hr160
  have hr159 : r159 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=159) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg196 : w 196=((1 / 1 : ℚ) * (w 194) * (w 195)) := by dsimp only [r159] at hr159; linear_combination hr159
  have hr158 : r158 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=158) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg195 : w 195=((1 / 1 : ℚ) * (w 194) * (w 194)) := by dsimp only [r158] at hr158; linear_combination hr158
  dsimp only [F1,t1,contactPolynomial]
  rw [hg197,hg196,hg195]
  ring

theorem qd1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q1 S w*(delta1 S w)^3=e1 S w := by
  have hr165 : r165 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=165) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg202 : w 202=((1 / 1 : ℚ) * (w 194) * (w 194) + (-1 / 2 : ℚ) * (w 194) * (w 195)) := by dsimp only [r165] at hr165; linear_combination hr165
  have hr158 : r158 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=158) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg195 : w 195=((1 / 1 : ℚ) * (w 194) * (w 194)) := by dsimp only [r158] at hr158; linear_combination hr158
  have hr166 : r166 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=166) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [e1,q1,t1,delta1,t1]
  dsimp only [r166] at hr166
  simp only [hg202,hg195] at hr166 ⊢
  linear_combination (1 / 1 : ℚ)*hr166

theorem ed1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ed1 S w=e1 S w*delta1 S w := by
  have hr167 : r167 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=167) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [e1,ed1,t1,delta1,t1]
  dsimp only [r167] at hr167
  linear_combination (1 / 1 : ℚ)*hr167

theorem aa1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    aa1 S w=(e1 S w)^2 := by
  have hr168 : r168 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=168) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [aa1,e1,delta1,t1]
  dsimp only [r168] at hr168
  linear_combination (1 / 1 : ℚ)*hr168

theorem cc1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    cc1 S w*delta1 S w=(aa1 S w)^2 := by
  have hr169 : r169 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=169) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [cc1,aa1,t1,delta1,t1]
  dsimp only [r169] at hr169
  linear_combination (1 / 1 : ℚ)*hr169

theorem xx1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    xx1 S w*ed1 S w=(cc1 S w)^2 := by
  have hr170 : r170 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=170) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [xx1,ed1,cc1,delta1,t1]
  dsimp only [r170] at hr170
  linear_combination (1 / 1 : ℚ)*hr170

theorem yy1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q1 S w*yy1 S w=(xx1 S w)^2 := by
  have hr171 : r171 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=171) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [q1,yy1,xx1,delta1,t1]
  dsimp only [r171] at hr171
  linear_combination (1 / 1 : ℚ)*hr171

theorem zz1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q1 S w*zz1 S w=(yy1 S w)^2 := by
  have hr172 : r172 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=172) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [q1,zz1,yy1,delta1,t1]
  dsimp only [r172] at hr172
  linear_combination (1 / 1 : ℚ)*hr172

theorem ad1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ad1 S w=A1 S w*delta1 S w := by
  have hr158 : r158 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=158) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg195 : w 195=((1 / 1 : ℚ) * (w 194) * (w 194)) := by dsimp only [r158] at hr158; linear_combination hr158
  have hr161 : r161 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=161) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr157 : r157 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=157) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [ad1,A1,delta1,t1]
  dsimp only [r161] at hr161
  dsimp only [r157] at hr157
  simp only [hg195] at hr161
  linear_combination (-1/1:ℚ)*hr161+(((1 / 1 : ℚ) * (w 194))-1)*(1/1:ℚ)*hr157

theorem eF1_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    e1 S w*F1 S w=(A1 S w*delta1 S w)^5 := by
  rw [←ad1_source S w source]
  have hr163 : r163 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=163) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg200 : w 200=((1 / 1 : ℚ) * (w 199) * (w 199)) := by dsimp only [r163] at hr163; linear_combination hr163
  have hr162 : r162 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=162) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg199 : w 199=((1 / 1 : ℚ) * (w 198) * (w 198)) := by dsimp only [r162] at hr162; linear_combination hr162
  have hr164 : r164 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=164) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [e1,F1,ad1]
  dsimp only [r164] at hr164
  simp only [hg200,hg199] at hr164 ⊢
  linear_combination (1/1:ℚ)*hr164

theorem weight1_valuations (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (R : ℤ)
    (hve : v (e1 S w)=(-R:ℤ)) (hvd : v (delta1 S w)=0) :
    v (q1 S w)=(-R:ℤ) ∧ v (xx1 S w)=(-7*R:ℤ) ∧
      v (zz1 S w)=(-25*R:ℤ) ∧ v (ed1 S w)=(-R:ℤ) := by
  have he : e1 S w≠0 := (v.ne_top_iff).mp (by rw [hve]; simp)
  exact LocalSoundness318.weight_values v _ _ _ _ _ _ _ _ _ R he hve hvd
    (qd1_source S w source) (ed1_source S w source)
    (aa1_source S w source) (cc1_source S w source)
    (xx1_source S w source) (yy1_source S w source) (zz1_source S w source)

theorem contact1_valuations (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (a f : ℤ)
    (hA : v (A1 S w)=a) (hF : v (F1 S w)=f)
    (hd : v (delta1 S w)=0) (ha : Even a) (hf : Odd f) :
    Odd (f-5*a) ∧ v (q1 S w)=(-(f-5*a):ℤ) ∧
      v (xx1 S w)=(-7*(f-5*a):ℤ) ∧ v (zz1 S w)=(-25*(f-5*a):ℤ) ∧
      v (ed1 S w)=(-(f-5*a):ℤ) := by
  have he := LocalSoundness318.contact_e_value v _ _ _ _ a f hA hF hd
    (eF1_source S w source)
  have hve : v (e1 S w)=(-(f-5*a):ℤ) := by simpa only [show 5*a-f=-(f-5*a) by ring] using he
  exact ⟨LocalSoundness318.contact_R_odd f a hf ha,
    weight1_valuations S w source v (f-5*a) hve hd⟩

@[expose] def t2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 245))
@[expose] def F2 (S : ℚ) (w : Assignment) : ℚ := ((-16 / 976393 : ℚ) * (w 245) + (76265 / 1952786 : ℚ) * (w 246) + (602706 / 976393 : ℚ) * (w 248))
@[expose] def e2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 252))
@[expose] def q2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 254))
@[expose] def ed2 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 1 : ℚ) * (w 252) + (1 / 1 : ℚ) * (w 255))
@[expose] def aa2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 256))
@[expose] def cc2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 257))
@[expose] def xx2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 258))
@[expose] def yy2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 259))
@[expose] def zz2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 260))
@[expose] def ad2 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 1 : ℚ) * (w 249))
@[expose] def delta2 (S : ℚ) (w : Assignment) : ℚ := t2 S w-1
@[expose] def A2 (S : ℚ) (w : Assignment) : ℚ := ((1 / 1 : ℚ) * (w 145) * (w 145))

theorem F2_actual (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    F2 S w=contactPolynomial (t2 S w) := by
  have hr213 : r213 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=213) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg248 : w 248=((1 / 1 : ℚ) * (w 245) * (w 246) + (3081901 / 1205412 : ℚ) * (w 246) * (w 246) + (976393 / 602706 : ℚ) * (w 246) * (w 247)) := by dsimp only [r213] at hr213; linear_combination hr213
  have hr212 : r212 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=212) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg247 : w 247=((1 / 1 : ℚ) * (w 245) * (w 246)) := by dsimp only [r212] at hr212; linear_combination hr212
  have hr211 : r211 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=211) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg246 : w 246=((1 / 1 : ℚ) * (w 245) * (w 245)) := by dsimp only [r211] at hr211; linear_combination hr211
  dsimp only [F2,t2,contactPolynomial]
  rw [hg248,hg247,hg246]
  ring

theorem qd2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q2 S w*(delta2 S w)^3=e2 S w := by
  have hr218 : r218 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=218) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg253 : w 253=((1 / 1 : ℚ) * (w 245) * (w 245) + (-1 / 2 : ℚ) * (w 245) * (w 246)) := by dsimp only [r218] at hr218; linear_combination hr218
  have hr211 : r211 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=211) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg246 : w 246=((1 / 1 : ℚ) * (w 245) * (w 245)) := by dsimp only [r211] at hr211; linear_combination hr211
  have hr219 : r219 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=219) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [e2,q2,t2,delta2,t2]
  dsimp only [r219] at hr219
  simp only [hg253,hg246] at hr219 ⊢
  linear_combination (1 / 1 : ℚ)*hr219

theorem ed2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ed2 S w=e2 S w*delta2 S w := by
  have hr220 : r220 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=220) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [e2,ed2,t2,delta2,t2]
  dsimp only [r220] at hr220
  linear_combination (1 / 1 : ℚ)*hr220

theorem aa2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    aa2 S w=(e2 S w)^2 := by
  have hr221 : r221 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=221) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [aa2,e2,delta2,t2]
  dsimp only [r221] at hr221
  linear_combination (1 / 1 : ℚ)*hr221

theorem cc2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    cc2 S w*delta2 S w=(aa2 S w)^2 := by
  have hr222 : r222 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=222) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [cc2,aa2,t2,delta2,t2]
  dsimp only [r222] at hr222
  linear_combination (1 / 1 : ℚ)*hr222

theorem xx2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    xx2 S w*ed2 S w=(cc2 S w)^2 := by
  have hr223 : r223 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=223) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [xx2,ed2,cc2,delta2,t2]
  dsimp only [r223] at hr223
  linear_combination (1 / 1 : ℚ)*hr223

theorem yy2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q2 S w*yy2 S w=(xx2 S w)^2 := by
  have hr224 : r224 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=224) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [q2,yy2,xx2,delta2,t2]
  dsimp only [r224] at hr224
  linear_combination (1 / 1 : ℚ)*hr224

theorem zz2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    q2 S w*zz2 S w=(yy2 S w)^2 := by
  have hr225 : r225 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=225) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [q2,zz2,yy2,delta2,t2]
  dsimp only [r225] at hr225
  linear_combination (1 / 1 : ℚ)*hr225

theorem ad2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    ad2 S w=A2 S w*delta2 S w := by
  have hr211 : r211 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=211) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg246 : w 246=((1 / 1 : ℚ) * (w 245) * (w 245)) := by dsimp only [r211] at hr211; linear_combination hr211
  have hr214 : r214 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=214) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hr210 : r210 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=210) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [ad2,A2,delta2,t2]
  dsimp only [r214] at hr214
  dsimp only [r210] at hr210
  simp only [hg246] at hr214
  linear_combination (-1/1:ℚ)*hr214+(((1 / 1 : ℚ) * (w 245))-1)*(1/1:ℚ)*hr210

theorem eF2_source (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w) :
    e2 S w*F2 S w=(A2 S w*delta2 S w)^5 := by
  rw [←ad2_source S w source]
  have hr216 : r216 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=216) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg251 : w 251=((1 / 1 : ℚ) * (w 250) * (w 250)) := by dsimp only [r216] at hr216; linear_combination hr216
  have hr215 : r215 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=215) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  have hg250 : w 250=((1 / 1 : ℚ) * (w 249) * (w 249)) := by dsimp only [r215] at hr215; linear_combination hr215
  have hr217 : r217 S w=0 := source _ (List.getElem_mem (l:=stage0 S) (n:=217) (by simp only [stage0,List.length_cons,List.length_nil]; decide))
  dsimp only [e2,F2,ad2]
  dsimp only [r217] at hr217
  simp only [hg251,hg250] at hr217 ⊢
  linear_combination (1/1:ℚ)*hr217

theorem weight2_valuations (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (R : ℤ)
    (hve : v (e2 S w)=(-R:ℤ)) (hvd : v (delta2 S w)=0) :
    v (q2 S w)=(-R:ℤ) ∧ v (xx2 S w)=(-7*R:ℤ) ∧
      v (zz2 S w)=(-25*R:ℤ) ∧ v (ed2 S w)=(-R:ℤ) := by
  have he : e2 S w≠0 := (v.ne_top_iff).mp (by rw [hve]; simp)
  exact LocalSoundness318.weight_values v _ _ _ _ _ _ _ _ _ R he hve hvd
    (qd2_source S w source) (ed2_source S w source)
    (aa2_source S w source) (cc2_source S w source)
    (xx2_source S w source) (yy2_source S w source) (zz2_source S w source)

theorem contact2_valuations (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (v : AddValuation ℚ (WithTop ℤ)) (a f : ℤ)
    (hA : v (A2 S w)=a) (hF : v (F2 S w)=f)
    (hd : v (delta2 S w)=0) (ha : Even a) (hf : Odd f) :
    Odd (f-5*a) ∧ v (q2 S w)=(-(f-5*a):ℤ) ∧
      v (xx2 S w)=(-7*(f-5*a):ℤ) ∧ v (zz2 S w)=(-25*(f-5*a):ℤ) ∧
      v (ed2 S w)=(-(f-5*a):ℤ) := by
  have he := LocalSoundness318.contact_e_value v _ _ _ _ a f hA hF hd
    (eF2_source S w source)
  have hve : v (e2 S w)=(-(f-5*a):ℤ) := by simpa only [show 5*a-f=-(f-5*a) by ring] using he
  exact ⟨LocalSoundness318.contact_R_odd f a hf ha,
    weight2_valuations S w source v (f-5*a) hve hd⟩

end RawWeights318
