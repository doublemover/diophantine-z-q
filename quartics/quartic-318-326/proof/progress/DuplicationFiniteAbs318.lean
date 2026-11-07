module
public import RelativeDuplicationHeight318
public section
namespace DuplicationFiniteAbs318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem primitive_lower_bound {F:Type*} [Field F] (v:AbsoluteValue F ℝ)
    (hna:IsNonarchimedean v) (a b D:F)
    (hD:v D≤1) (h2:v (2:F)≤1) (hp:max (v a) (v b)=1) :
    v (2:F)^3*v D^2≤max (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2))) := by
  have ha:v a≤1 := (le_max_left _ _).trans_eq hp
  have hb:v b≤1 := (le_max_right _ _).trans_eq hp
  have ha0:=apply_nonneg v a
  have hb0:=apply_nonneg v b
  have hd0:=apply_nonneg v D
  have he0:=apply_nonneg v (2:F)
  have hfour:v (4:F)=v (2:F)^2 := by rw [show (4:F)=2^2 by ring,map_pow]
  by_cases hs:v (2:F)*v D≤v (a^2+D*b^2)
  · apply le_trans _ (le_max_left _ _)
    rw [map_pow]
    have hbase:0≤v (2:F)*v D := mul_nonneg he0 hd0
    have hsq := (sq_le_sq₀ hbase (apply_nonneg v _)).mpr hs
    have hprod := mul_le_of_le_one_right (sq_nonneg (v (2:F)*v D)) h2
    nlinarith
  · have hs':v (a^2+D*b^2)<v (2:F)*v D := lt_of_not_ge hs
    have hB:v b=1 := by
      by_contra hn
      have hb':v b<1 := lt_of_le_of_ne hb hn
      have hA:v a=1 := by
        rcases le_total (v a) (v b) with hab|hba
        · rw [max_eq_right hab] at hp; exact False.elim (hn hp)
        · simpa [max_eq_left hba] using hp
      have hvb:v (D*b^2)<v (a^2) := by
        rw [map_mul,map_pow,map_pow,hA]
        have hh := mul_le_of_le_one_left (sq_nonneg (v b)) hD
        nlinarith
      have hsum:v (a^2+D*b^2)=1 := by
        rw [hna.add_eq_left_of_lt (map_neg_eq_map v) hvb,map_pow,hA]
        norm_num
      rw [hsum] at hs'
      have hh : v (2:F)*v D≤1 := (mul_le_of_le_one_left hd0 h2).trans hD
      linarith
    have hDb:v (D*b^2)=v D := by rw [map_mul,map_pow,hB]; norm_num
    have hsD:v (a^2+D*b^2)<v D := hs'.trans_le (mul_le_of_le_one_left hd0 h2)
    have hA:v a^2=v D := by
      have hh := hna.add_eq_right_of_lt (map_neg_eq_map v)
        (show v (a^2+D*b^2)<v (-(D*b^2)) by simpa [map_neg_eq_map,hDb] using hsD)
      have he:(a^2+D*b^2)+-(D*b^2)=a^2 := by ring
      rw [he,map_pow,map_neg_eq_map,hDb] at hh
      exact hh
    have hsmall:v D≤v a := by nlinarith
    have htwo:v (2*D*b^2)=v (2:F)*v D := by rw [map_mul,map_mul,map_pow,hB]; ring
    have ht:v (a^2-D*b^2)=v (2:F)*v D := by
      have hh := hna.add_eq_right_of_lt (map_neg_eq_map v)
        (show v (a^2+D*b^2)<v (-(2*D*b^2)) by simpa [map_neg_eq_map,htwo] using hs')
      have he:(a^2+D*b^2)+-(2*D*b^2)=a^2-D*b^2 := by ring
      simpa only [he,map_neg_eq_map,htwo] using hh
    apply le_trans _ (le_max_right _ _)
    rw [map_mul,map_mul,map_mul,hfour,hB,ht]
    have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall hd0)
      (pow_nonneg he0 3)
    nlinarith

theorem primitive_upper_bound {F:Type*} [Field F] (v:AbsoluteValue F ℝ)
    (hna:IsNonarchimedean v) (a b D:F)
    (hD:v D≤1) (h2:v (2:F)≤1) (hp:max (v a) (v b)=1) :
    max (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))≤1 := by
  have ha:v a≤1 := (le_max_left _ _).trans_eq hp
  have hb:v b≤1 := (le_max_right _ _).trans_eq hp
  have ha2:v (a^2)≤1 := by rw [map_pow]; simpa using (sq_le_sq₀ (apply_nonneg v a) (by norm_num)).mpr ha
  have hb2:v (b^2)≤1 := by rw [map_pow]; simpa using (sq_le_sq₀ (apply_nonneg v b) (by norm_num)).mpr hb
  have hDb:v (D*b^2)≤1 := by
    rw [map_mul]
    exact (mul_le_of_le_one_left (apply_nonneg v _) hD).trans hb2
  have hs:v (a^2+D*b^2)≤1 := (hna _ _).trans (max_le ha2 hDb)
  have ht:v (a^2-D*b^2)≤1 := by
    simpa only [sub_eq_add_neg,map_neg_eq_map] using (hna (a^2) (-(D*b^2))).trans (max_le ha2 (by simpa only [map_neg_eq_map] using hDb))
  have h4:v (4:F)≤1 := by
    rw [show (4:F)=2^2 by ring,map_pow]
    simpa using (sq_le_sq₀ (apply_nonneg v (2:F)) (by norm_num)).mpr h2
  apply max_le
  · rw [map_pow]
    simpa using (sq_le_sq₀ (apply_nonneg v _) (by norm_num)).mpr hs
  · rw [map_mul,map_mul,map_mul]
    have h4a : v (4:F)*v a≤1 := (mul_le_of_le_one_left (apply_nonneg v a) h4).trans ha
    have h4ab : v (4:F)*v a*v b≤1 := (mul_le_of_le_one_left (apply_nonneg v b) h4a).trans hb
    exact (mul_le_of_le_one_left (apply_nonneg v _) h4ab).trans ht

theorem primitive_scaling {F:Type*} [Field F] (v:AbsoluteValue F ℝ) (a b:F)
    (hab:a≠0 ∨ b≠0) : ∃(c a' b':F),c≠0 ∧ a=c*a' ∧ b=c*b' ∧
      max (v a') (v b')=1 ∧ v c=max (v a) (v b) := by
  rcases le_total (v a) (v b) with hle|hle
  · have hb:b≠0 := by
      intro hb
      have ha:a=0 := (map_eq_zero v).mp (by rw [hb,map_zero] at hle; exact le_antisymm hle (apply_nonneg v a))
      exact hab.elim (fun h => h ha) (fun h => h hb)
    refine ⟨b,a/b,1,hb,?_,by ring,?_,(max_eq_right hle).symm⟩
    · field_simp [hb]
    · rw [map_one,map_div₀,max_eq_right]
      exact (div_le_one₀ (map_pos_of_ne_zero v hb)).mpr hle
  · have ha:a≠0 := by
      intro ha
      have hb:b=0 := (map_eq_zero v).mp (by rw [ha,map_zero] at hle; exact le_antisymm hle (apply_nonneg v b))
      exact hab.elim (fun h => h ha) (fun h => h hb)
    refine ⟨a,1,b/a,ha,by ring,?_,?_,(max_eq_left hle).symm⟩
    · field_simp [ha]
    · rw [map_one,map_div₀,max_eq_left]
      exact (div_le_one₀ (map_pos_of_ne_zero v ha)).mpr hle

theorem absolute_duplication_bounds {F:Type*} [Field F] (v:AbsoluteValue F ℝ)
    (hna:IsNonarchimedean v) (a b D:F) (hD:v D≤1) (h2:v (2:F)≤1) :
    v (2:F)^3*v D^2*(max (v a) (v b))^4≤
      max (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2))) ∧
    max (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))≤(max (v a) (v b))^4 := by
  by_cases hzero:a=0 ∧ b=0
  · rcases hzero with ⟨rfl,rfl⟩; simp
  have hab:a≠0 ∨ b≠0 := by tauto
  obtain ⟨c,a',b',hc,ha,hb,hp,hm⟩ := primitive_scaling v a b hab
  have hF:(a^2+D*b^2)^2=c^4*(a'^2+D*b'^2)^2 := by rw [ha,hb]; ring
  have hG:4*a*b*(a^2-D*b^2)=c^4*(4*a'*b'*(a'^2-D*b'^2)) := by rw [ha,hb]; ring
  have heq : max (v ((a^2+D*b^2)^2)) (v (4*a*b*(a^2-D*b^2)))=
      v c^4*max (v ((a'^2+D*b'^2)^2)) (v (4*a'*b'*(a'^2-D*b'^2))) := by
    rw [hF,hG,map_mul,map_mul,map_pow,mul_max_of_nonneg _ _ (pow_nonneg (apply_nonneg v c) 4)]
  rw [heq,←hm]
  constructor
  · have hh := mul_le_mul_of_nonneg_left (primitive_lower_bound v hna a' b' D hD h2 hp)
      (pow_nonneg (apply_nonneg v c) 4)
    simpa only [mul_comm (v c^4)] using hh
  · simpa using mul_le_mul_of_nonneg_left (primitive_upper_bound v hna a' b' D hD h2 hp)
      (pow_nonneg (apply_nonneg v c) 4)

end DuplicationFiniteAbs318
