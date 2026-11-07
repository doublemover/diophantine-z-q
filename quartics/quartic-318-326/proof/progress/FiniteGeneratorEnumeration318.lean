module
public import FiniteGeneratorChunk1318
public import FiniteGeneratorChunk2318
public import FiniteGeneratorChunk3318
public import FiniteGeneratorChunk4318
public import FiniteGeneratorChunk5318
public import FiniteGeneratorChunk6318
public import FiniteGeneratorChunk7318
public import FiniteGeneratorChunk8318
public import FiniteGeneratorChunk9318
public import GlobalGeneratorPoints318
public import RationalCandidates318
public section
namespace FiniteGeneratorEnumeration318
open FiniteSquareTest318 ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem bounded_leading (a:ℕ) (ha:1≤a) (hA:a≤81) : CheckLeading a := by
  interval_cases a
  · exact leading_1
  · exact leading_2
  · exact leading_3
  · exact leading_4
  · exact leading_5
  · exact leading_6
  · exact leading_7
  · exact leading_8
  · exact leading_9
  · exact leading_10
  · exact leading_11
  · exact leading_12
  · exact leading_13
  · exact leading_14
  · exact leading_15
  · exact leading_16
  · exact leading_17
  · exact leading_18
  · exact leading_19
  · exact leading_20
  · exact leading_21
  · exact leading_22
  · exact leading_23
  · exact leading_24
  · exact leading_25
  · exact leading_26
  · exact leading_27
  · exact leading_28
  · exact leading_29
  · exact leading_30
  · exact leading_31
  · exact leading_32
  · exact leading_33
  · exact leading_34
  · exact leading_35
  · exact leading_36
  · exact leading_37
  · exact leading_38
  · exact leading_39
  · exact leading_40
  · exact leading_41
  · exact leading_42
  · exact leading_43
  · exact leading_44
  · exact leading_45
  · exact leading_46
  · exact leading_47
  · exact leading_48
  · exact leading_49
  · exact leading_50
  · exact leading_51
  · exact leading_52
  · exact leading_53
  · exact leading_54
  · exact leading_55
  · exact leading_56
  · exact leading_57
  · exact leading_58
  · exact leading_59
  · exact leading_60
  · exact leading_61
  · exact leading_62
  · exact leading_63
  · exact leading_64
  · exact leading_65
  · exact leading_66
  · exact leading_67
  · exact leading_68
  · exact leading_69
  · exact leading_70
  · exact leading_71
  · exact leading_72
  · exact leading_73
  · exact leading_74
  · exact leading_75
  · exact leading_76
  · exact leading_77
  · exact leading_78
  · exact leading_79
  · exact leading_80
  · exact leading_81

/-- Exhaustive kernel-checked quadratic coefficient box, including both
signs of sqrt(2) and the exact primitive-polynomial divisibility test. -/
theorem bounded_quadratic (a:ℕ) (b:ℤ) (k:ℕ)
    (ha:1≤a) (hA:a≤81) (hb:-162≤b) (hB:b≤162) (hk:1≤k) (hK:k≤162) :
    CheckCandidate a b k := by
  have h := bounded_leading a ha hA ⟨(b+162).toNat,by omega⟩ ⟨k-1,by omega⟩
  have hb' : (((b+162).toNat:ℕ):ℤ)-162=b := by omega
  have hk' : k-1+1=k := by omega
  simpa only [hb',hk'] using h


@[expose] def CandidateCoordinates (u v:ℚ) : Prop :=
  (∃(a:ℤ)(b:ℕ),-9≤a ∧ a≤9 ∧ 1≤b ∧ b≤9 ∧ u=(a:ℚ)/b ∧ v=0) ∨
  (∃(a:ℕ)(b:ℤ)(k:ℕ),1≤a ∧ a≤81 ∧ -162≤b ∧ b≤162 ∧ 1≤k ∧ k≤162 ∧
    PrimitiveCandidate a b k ∧ u= -(b:ℚ)/(2*a) ∧
    (v=(k:ℚ)/(2*a) ∨ v= -(k:ℚ)/(2*a)))

@[expose] def CandidatePoint (Q:E.Point) : Prop :=
  ∃(u v:ℚ)(y:K)(h:E.Nonsingular (pair u v) y),Q=Point.some _ y h ∧ CandidateCoordinates u v

theorem candidate_survivor (u v:ℚ) (hc:CandidateCoordinates u v) (he:CurveTest u v) :
    Survivor u v := by
  rcases hc with ⟨a,b,ha,hA,hb,hB,rfl,rfl⟩ | ⟨a,b,k,ha,hA,hb,hB,hk,hK,hp,rfl,hv⟩
  · exact bounded_rational a b ha hA hb hB he
  · have hh := bounded_quadratic a b k ha hA hb hB hk hK hp
    rcases hv with rfl|rfl
    · exact hh.1 he
    · exact hh.2 he

/-- The bounded arithmetic certificate is now attached to actual curve
points and actual torsion translates, not merely to a list of coordinates. -/
theorem candidate_classified (Q:E.Point) (hc:CandidatePoint Q) :
    GlobalGeneratorPoints318.Classified Q := by
  obtain ⟨u,v,y,h,rfl,hc⟩ := hc
  apply GlobalGeneratorPoints318.classified_survivor u v y h
  exact candidate_survivor u v hc (curve_test_of_equation u v y h.1)

end FiniteGeneratorEnumeration318
