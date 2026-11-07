module

public import AnchorValueShear

public section

namespace Raw318FinalReplay

open CircuitReplay

set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option linter.unusedSimpArgs false

set_option linter.unusedVariables false

set_option linter.unnecessarySimpa false

set_option linter.unnecessarySeqFocus false



@[expose] def r0 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 1 * w 1) + (-2 * w 2 * w 2) + (1 * w 58)

@[expose] def r1 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 1 * w 2) + (1 * w 59)

@[expose] def r2 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 3 * w 3) + (2 * w 4 * w 4) + (11 * w 58 * w 58) + (-48 * w 58 * w 59) + (88 * w 59 * w 59)

@[expose] def r3 (S : ℚ) (w : Assignment) : ℚ := (2 * w 3 * w 4) + (-6 * w 58 * w 58) + (44 * w 58 * w 59) + (-48 * w 59 * w 59)

@[expose] def r4 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 5 * w 5) + (-2 * w 6 * w 6) + (1 * w 60)

@[expose] def r5 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 5 * w 6) + (1 * w 61)

@[expose] def r6 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 7 * w 7) + (2 * w 8 * w 8) + (11 * w 60 * w 60) + (-48 * w 60 * w 61) + (88 * w 61 * w 61)

@[expose] def r7 (S : ℚ) (w : Assignment) : ℚ := (2 * w 7 * w 8) + (-6 * w 60 * w 60) + (44 * w 60 * w 61) + (-48 * w 61 * w 61)

@[expose] def r8 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 2) * w 9 * w 9) + (-1 * w 10 * w 10) + (1 * w 62)

@[expose] def r9 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 9 * w 10) + (1 * w 63)

@[expose] def r10 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 11 * w 11) + (2 * w 12 * w 12) + (44 * w 62 * w 62) + (-96 * w 62 * w 63) + (88 * w 63 * w 63)

@[expose] def r11 (S : ℚ) (w : Assignment) : ℚ := (2 * w 11 * w 12) + (-24 * w 62 * w 62) + (88 * w 62 * w 63) + (-48 * w 63 * w 63)

@[expose] def r12 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 13 * w 13) + (-2 * w 14 * w 14) + (1 * w 64)

@[expose] def r13 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 13 * w 14) + (1 * w 65)

@[expose] def r14 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 15 * w 15) + (2 * w 16 * w 16) + (11 * w 64 * w 64) + (-48 * w 64 * w 65) + (88 * w 65 * w 65)

@[expose] def r15 (S : ℚ) (w : Assignment) : ℚ := (2 * w 15 * w 16) + (-6 * w 64 * w 64) + (44 * w 64 * w 65) + (-48 * w 65 * w 65)

@[expose] def r16 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 17 * w 17) + (-2 * w 18 * w 18) + (1 * w 66)

@[expose] def r17 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 17 * w 18) + (1 * w 67)

@[expose] def r18 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 19 * w 19) + (2 * w 20 * w 20) + (11 * w 66 * w 66) + (-48 * w 66 * w 67) + (88 * w 67 * w 67)

@[expose] def r19 (S : ℚ) (w : Assignment) : ℚ := (2 * w 19 * w 20) + (-6 * w 66 * w 66) + (44 * w 66 * w 67) + (-48 * w 67 * w 67)

@[expose] def r20 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 21 * w 21) + (-2 * w 22 * w 22) + (1 * w 68)

@[expose] def r21 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 21 * w 22) + (1 * w 69)

@[expose] def r22 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 23 * w 23) + (2 * w 24 * w 24) + (11 * w 68 * w 68) + (-48 * w 68 * w 69) + (88 * w 69 * w 69)

@[expose] def r23 (S : ℚ) (w : Assignment) : ℚ := (2 * w 23 * w 24) + (-6 * w 68 * w 68) + (44 * w 68 * w 69) + (-48 * w 69 * w 69)

@[expose] def r24 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 25 * w 25) + (-2 * w 26 * w 26) + (1 * w 70)

@[expose] def r25 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 25 * w 26) + (1 * w 71)

@[expose] def r26 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 27 * w 27) + (2 * w 28 * w 28) + (11 * w 70 * w 70) + (-48 * w 70 * w 71) + (88 * w 71 * w 71)

@[expose] def r27 (S : ℚ) (w : Assignment) : ℚ := (2 * w 27 * w 28) + (-6 * w 70 * w 70) + (44 * w 70 * w 71) + (-48 * w 71 * w 71)

@[expose] def r28 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 29 * w 29) + (-2 * w 30 * w 30) + (1 * w 72)

@[expose] def r29 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 29 * w 30) + (1 * w 73)

@[expose] def r30 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 31 * w 31) + (2 * w 32 * w 32) + (11 * w 72 * w 72) + (-48 * w 72 * w 73) + (88 * w 73 * w 73)

@[expose] def r31 (S : ℚ) (w : Assignment) : ℚ := (2 * w 31 * w 32) + (-6 * w 72 * w 72) + (44 * w 72 * w 73) + (-48 * w 73 * w 73)

@[expose] def r32 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 33 * w 35) + (-2 * w 34 * w 36) + (1 * w 74)

@[expose] def r33 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 33 * w 36) + (-1 * w 34 * w 35) + (1 * w 75)

@[expose] def r34 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 35 * w 74) + (-2 * w 36 * w 75) + (1 * w 76)

@[expose] def r35 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 35 * w 75) + (-1 * w 36 * w 74) + (1 * w 77)

@[expose] def r36 (S : ℚ) (w : Assignment) : ℚ := (1) + ((-57 / 8) * w 33) + (7 * w 34) + ((-39 / 4) * w 74) + (-11 * w 74 * w 74) + (24 * w 74 * w 75) + (18 * w 75) + (-22 * w 75 * w 75) + ((-57 / 8) * w 76) + (7 * w 77)

@[expose] def r37 (S : ℚ) (w : Assignment) : ℚ := ((7 / 2) * w 33) + ((-57 / 8) * w 34) + (9 * w 74) + (6 * w 74 * w 74) + (-22 * w 74 * w 75) + ((-39 / 4) * w 75) + (12 * w 75 * w 75) + ((7 / 2) * w 76) + ((-57 / 8) * w 77)

@[expose] def r38 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 33 * w 33) + (2 * w 34 * w 34) + (1 * w 37 * w 37)

@[expose] def r39 (S : ℚ) (w : Assignment) : ℚ := (-1) + (-1 * w 58 * w 78) + (1 * w 66 * w 78)

@[expose] def r40 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 1 * w 19) + (-2 * w 2 * w 20) + (-1 * w 3 * w 17) + (-2 * w 4 * w 18) + (-1 * w 58 * w 79) + (-4 * w 59 * w 80) + (1 * w 66 * w 79) + (4 * w 67 * w 80)

@[expose] def r41 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 1 * w 20) + (-1 * w 2 * w 19) + (-1 * w 3 * w 18) + (-1 * w 4 * w 17) + (-1 * w 58 * w 80) + (-2 * w 59 * w 79) + (1 * w 66 * w 80) + (2 * w 67 * w 79)

@[expose] def r42 (S : ℚ) (w : Assignment) : ℚ := (-1) + (-1 * w 60 * w 81) + (1 * w 68 * w 81)

@[expose] def r43 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 5 * w 23) + (-2 * w 6 * w 24) + (-1 * w 7 * w 21) + (-2 * w 8 * w 22) + (-1 * w 60 * w 82) + (-4 * w 61 * w 83) + (1 * w 68 * w 82) + (4 * w 69 * w 83)

@[expose] def r44 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 5 * w 24) + (-1 * w 6 * w 23) + (-1 * w 7 * w 22) + (-1 * w 8 * w 21) + (-1 * w 60 * w 83) + (-2 * w 61 * w 82) + (1 * w 68 * w 83) + (2 * w 69 * w 82)

@[expose] def r45 (S : ℚ) (w : Assignment) : ℚ := (-1) + (-2 * w 62 * w 84) + (1 * w 70 * w 84)

@[expose] def r46 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 9 * w 27) + (-2 * w 10 * w 28) + (-1 * w 11 * w 25) + (-2 * w 12 * w 26) + (-2 * w 62 * w 85) + (-4 * w 63 * w 86) + (1 * w 70 * w 85) + (4 * w 71 * w 86)

@[expose] def r47 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 9 * w 28) + (-1 * w 10 * w 27) + (-1 * w 11 * w 26) + (-1 * w 12 * w 25) + (-2 * w 62 * w 86) + (-2 * w 63 * w 85) + (1 * w 70 * w 86) + (2 * w 71 * w 85)

@[expose] def r48 (S : ℚ) (w : Assignment) : ℚ := (-1) + (-1 * w 64 * w 87) + (1 * w 72 * w 87)

@[expose] def r49 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 13 * w 31) + (-2 * w 14 * w 32) + (-1 * w 15 * w 29) + (-2 * w 16 * w 30) + (-1 * w 64 * w 88) + (-4 * w 65 * w 89) + (1 * w 72 * w 88) + (4 * w 73 * w 89)

@[expose] def r50 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 13 * w 32) + (-1 * w 14 * w 31) + (-1 * w 15 * w 30) + (-1 * w 16 * w 29) + (-1 * w 64 * w 89) + (-2 * w 65 * w 88) + (1 * w 72 * w 89) + (2 * w 73 * w 88)

@[expose] def r51 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 76 * w 76) + (-2 * w 77 * w 77) + (1 * w 90)

@[expose] def r52 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 76 * w 77) + (1 * w 91)

@[expose] def r53 (S : ℚ) (w : Assignment) : ℚ := (-1) + ((671 / 65) * w 90) + ((-3088 / 195) * w 90 * w 90) + ((5632 / 65) * w 90 * w 91) + ((-77 / 13) * w 90 * w 92) + ((84 / 13) * w 90 * w 93) + ((-1464 / 65) * w 91) + ((-24704 / 195) * w 91 * w 91) + ((168 / 13) * w 91 * w 92) + ((-308 / 13) * w 91 * w 93) + (1 * w 92)

@[expose] def r54 (S : ℚ) (w : Assignment) : ℚ := ((-366 / 65) * w 90) + ((704 / 65) * w 90 * w 90) + ((-12352 / 195) * w 90 * w 91) + ((42 / 13) * w 90 * w 92) + ((-77 / 13) * w 90 * w 93) + ((1342 / 65) * w 91) + ((5632 / 65) * w 91 * w 91) + ((-154 / 13) * w 91 * w 92) + ((168 / 13) * w 91 * w 93) + (1 * w 93)

@[expose] def r55 (S : ℚ) (w : Assignment) : ℚ := (1 * w 35 * w 92) + ((-7 / 2) * w 35 * w 93) + ((39 / 8) * w 35 * w 94) + (-9 * w 35 * w 95) + ((-7 / 2) * w 36 * w 92) + (2 * w 36 * w 93) + (-9 * w 36 * w 94) + ((39 / 4) * w 36 * w 95) + (11 * w 76 * w 94) + (-12 * w 76 * w 95) + (-12 * w 77 * w 94) + (22 * w 77 * w 95) + ((57 / 8) * w 94) + (-7 * w 95)

@[expose] def r56 (S : ℚ) (w : Assignment) : ℚ := ((-7 / 4) * w 35 * w 92) + (1 * w 35 * w 93) + ((-9 / 2) * w 35 * w 94) + ((39 / 8) * w 35 * w 95) + (1 * w 36 * w 92) + ((-7 / 2) * w 36 * w 93) + ((39 / 8) * w 36 * w 94) + (-9 * w 36 * w 95) + (-6 * w 76 * w 94) + (11 * w 76 * w 95) + (11 * w 77 * w 94) + (-12 * w 77 * w 95) + ((-7 / 2) * w 94) + ((57 / 8) * w 95)

@[expose] def r57 (S : ℚ) (w : Assignment) : ℚ := ((-157 / 195)) + ((-8 / 39) * w 23) + ((2 / 195) * w 23 * w 23) + ((5 / 13) * w 23 * w 96) + ((4 / 195) * w 24 * w 24) + ((10 / 13) * w 24 * w 97) + ((8 / 13) * w 96)

@[expose] def r58 (S : ℚ) (w : Assignment) : ℚ := ((4 / 195) * w 23 * w 24) + ((5 / 13) * w 23 * w 97) + ((-8 / 39) * w 24) + ((5 / 13) * w 24 * w 96) + ((8 / 13) * w 97)

@[expose] def r59 (S : ℚ) (w : Assignment) : ℚ := ((-157 / 195)) + ((-8 / 39) * w 27) + ((2 / 195) * w 27 * w 27) + ((5 / 13) * w 27 * w 98) + ((4 / 195) * w 28 * w 28) + ((10 / 13) * w 28 * w 99) + ((8 / 13) * w 98)

@[expose] def r60 (S : ℚ) (w : Assignment) : ℚ := ((4 / 195) * w 27 * w 28) + ((5 / 13) * w 27 * w 99) + ((-8 / 39) * w 28) + ((5 / 13) * w 28 * w 98) + ((8 / 13) * w 99)

@[expose] def r61 (S : ℚ) (w : Assignment) : ℚ := ((-157 / 195)) + ((-8 / 39) * w 31) + ((2 / 195) * w 31 * w 31) + ((5 / 13) * w 31 * w 100) + ((4 / 195) * w 32 * w 32) + ((10 / 13) * w 32 * w 101) + ((8 / 13) * w 100)

@[expose] def r62 (S : ℚ) (w : Assignment) : ℚ := ((4 / 195) * w 31 * w 32) + ((5 / 13) * w 31 * w 101) + ((-8 / 39) * w 32) + ((5 / 13) * w 32 * w 100) + ((8 / 13) * w 101)

@[expose] def r63 (S : ℚ) (w : Assignment) : ℚ := ((-39 / 8) * w 1) + ((-57 / 8) * w 1 * w 35) + (7 * w 1 * w 36) + (-11 * w 1 * w 74) + (12 * w 1 * w 75) + (9 * w 2) + (7 * w 2 * w 35) + ((-57 / 4) * w 2 * w 36) + (12 * w 2 * w 74) + (-22 * w 2 * w 75) + (-1 * w 3 * w 102) + ((7 / 2) * w 3 * w 103) + ((7 / 2) * w 4 * w 102) + (-2 * w 4 * w 103)

@[expose] def r64 (S : ℚ) (w : Assignment) : ℚ := ((9 / 2) * w 1) + ((7 / 2) * w 1 * w 35) + ((-57 / 8) * w 1 * w 36) + (6 * w 1 * w 74) + (-11 * w 1 * w 75) + ((-39 / 8) * w 2) + ((-57 / 8) * w 2 * w 35) + (7 * w 2 * w 36) + (-11 * w 2 * w 74) + (12 * w 2 * w 75) + ((7 / 4) * w 3 * w 102) + (-1 * w 3 * w 103) + (-1 * w 4 * w 102) + ((7 / 2) * w 4 * w 103)

@[expose] def r65 (S : ℚ) (w : Assignment) : ℚ := ((6 / 5) * w 17) + ((-1 / 5) * w 17 * w 19) + ((-2 / 5) * w 18 * w 20) + (1 * w 94 * w 104) + (2 * w 95 * w 105)

@[expose] def r66 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 5) * w 17 * w 20) + ((6 / 5) * w 18) + ((-1 / 5) * w 18 * w 19) + (1 * w 94 * w 105) + (1 * w 95 * w 104)

@[expose] def r67 (S : ℚ) (w : Assignment) : ℚ := ((-39 / 8) * w 5) + ((-57 / 8) * w 5 * w 35) + (7 * w 5 * w 36) + (-11 * w 5 * w 74) + (12 * w 5 * w 75) + (9 * w 6) + (7 * w 6 * w 35) + ((-57 / 4) * w 6 * w 36) + (12 * w 6 * w 74) + (-22 * w 6 * w 75) + (-1 * w 7 * w 106) + ((7 / 2) * w 7 * w 107) + ((7 / 2) * w 8 * w 106) + (-2 * w 8 * w 107)

@[expose] def r68 (S : ℚ) (w : Assignment) : ℚ := ((9 / 2) * w 5) + ((7 / 2) * w 5 * w 35) + ((-57 / 8) * w 5 * w 36) + (6 * w 5 * w 74) + (-11 * w 5 * w 75) + ((-39 / 8) * w 6) + ((-57 / 8) * w 6 * w 35) + (7 * w 6 * w 36) + (-11 * w 6 * w 74) + (12 * w 6 * w 75) + ((7 / 4) * w 7 * w 106) + (-1 * w 7 * w 107) + (-1 * w 8 * w 106) + ((7 / 2) * w 8 * w 107)

@[expose] def r69 (S : ℚ) (w : Assignment) : ℚ := (1 * w 21 * w 96) + (2 * w 22 * w 97) + (1 * w 94 * w 108) + (2 * w 95 * w 109)

@[expose] def r70 (S : ℚ) (w : Assignment) : ℚ := (1 * w 21 * w 97) + (1 * w 22 * w 96) + (1 * w 94 * w 109) + (1 * w 95 * w 108)

@[expose] def r71 (S : ℚ) (w : Assignment) : ℚ := ((-39 / 8) * w 9) + ((-57 / 8) * w 9 * w 35) + (7 * w 9 * w 36) + (-11 * w 9 * w 74) + (12 * w 9 * w 75) + (9 * w 10) + (7 * w 10 * w 35) + ((-57 / 4) * w 10 * w 36) + (12 * w 10 * w 74) + (-22 * w 10 * w 75) + (-1 * w 11 * w 110) + ((7 / 2) * w 11 * w 111) + ((7 / 2) * w 12 * w 110) + (-2 * w 12 * w 111)

@[expose] def r72 (S : ℚ) (w : Assignment) : ℚ := ((9 / 2) * w 9) + ((7 / 2) * w 9 * w 35) + ((-57 / 8) * w 9 * w 36) + (6 * w 9 * w 74) + (-11 * w 9 * w 75) + ((-39 / 8) * w 10) + ((-57 / 8) * w 10 * w 35) + (7 * w 10 * w 36) + (-11 * w 10 * w 74) + (12 * w 10 * w 75) + ((7 / 4) * w 11 * w 110) + (-1 * w 11 * w 111) + (-1 * w 12 * w 110) + ((7 / 2) * w 12 * w 111)

@[expose] def r73 (S : ℚ) (w : Assignment) : ℚ := (1 * w 25 * w 98) + (2 * w 26 * w 99) + (1 * w 94 * w 112) + (2 * w 95 * w 113)

@[expose] def r74 (S : ℚ) (w : Assignment) : ℚ := (1 * w 25 * w 99) + (1 * w 26 * w 98) + (1 * w 94 * w 113) + (1 * w 95 * w 112)

@[expose] def r75 (S : ℚ) (w : Assignment) : ℚ := ((-39 / 8) * w 13) + ((-57 / 8) * w 13 * w 35) + (7 * w 13 * w 36) + (-11 * w 13 * w 74) + (12 * w 13 * w 75) + (9 * w 14) + (7 * w 14 * w 35) + ((-57 / 4) * w 14 * w 36) + (12 * w 14 * w 74) + (-22 * w 14 * w 75) + (-1 * w 15 * w 114) + ((7 / 2) * w 15 * w 115) + ((7 / 2) * w 16 * w 114) + (-2 * w 16 * w 115)

@[expose] def r76 (S : ℚ) (w : Assignment) : ℚ := ((9 / 2) * w 13) + ((7 / 2) * w 13 * w 35) + ((-57 / 8) * w 13 * w 36) + (6 * w 13 * w 74) + (-11 * w 13 * w 75) + ((-39 / 8) * w 14) + ((-57 / 8) * w 14 * w 35) + (7 * w 14 * w 36) + (-11 * w 14 * w 74) + (12 * w 14 * w 75) + ((7 / 4) * w 15 * w 114) + (-1 * w 15 * w 115) + (-1 * w 16 * w 114) + ((7 / 2) * w 16 * w 115)

@[expose] def r77 (S : ℚ) (w : Assignment) : ℚ := (1 * w 29 * w 100) + (2 * w 30 * w 101) + (1 * w 94 * w 116) + (2 * w 95 * w 117)

@[expose] def r78 (S : ℚ) (w : Assignment) : ℚ := (1 * w 29 * w 101) + (1 * w 30 * w 100) + (1 * w 94 * w 117) + (1 * w 95 * w 116)

@[expose] def r79 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 0 * w 0) + (1 * w 118)

@[expose] def r80 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 106 * w 114) + (-2 * w 107 * w 115) + (1 * w 119)

@[expose] def r81 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 106 * w 115) + (-1 * w 107 * w 114) + (1 * w 120)

@[expose] def r82 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 106 * w 110) + (-2 * w 107 * w 111) + (1 * w 121)

@[expose] def r83 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 106 * w 111) + (-1 * w 107 * w 110) + (1 * w 122)

@[expose] def r84 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 110 * w 110) + (-2 * w 111 * w 111) + (-4 * w 114 * w 114) + (4 * w 114 * w 119) + (-2 * w 114 * w 121) + (-8 * w 115 * w 115) + (8 * w 115 * w 120) + (-4 * w 115 * w 122) + (-1 * w 119 * w 119) + (1 * w 119 * w 121) + (-2 * w 120 * w 120) + (2 * w 120 * w 122) + (1 * w 123)

@[expose] def r85 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 110 * w 111) + (-4 * w 114 * w 115) + (2 * w 114 * w 120) + (-1 * w 114 * w 122) + (2 * w 115 * w 119) + (-1 * w 115 * w 121) + (-1 * w 119 * w 120) + ((1 / 2) * w 119 * w 122) + ((1 / 2) * w 120 * w 121) + (1 * w 124)

@[expose] def r86 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 90 * w 90) + (8 * w 91 * w 91) + (1 * w 125)

@[expose] def r87 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 37 * w 37) + (1 * w 126)

@[expose] def r88 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 102 * w 102) + (2 * w 102 * w 104) + (-2 * w 103 * w 103) + (-4 * w 103 * w 105) + (-1 * w 104 * w 104) + (-2 * w 105 * w 105) + (1 * w 127)

@[expose] def r89 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 102 * w 103) + (-1 * w 102 * w 105) + (1 * w 103 * w 104) + (1 * w 104 * w 105) + (1 * w 128)

@[expose] def r90 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 106 * w 106) + (2 * w 106 * w 108) + (-2 * w 107 * w 107) + (-4 * w 107 * w 109) + (-1 * w 108 * w 108) + (-2 * w 109 * w 109) + (1 * w 129)

@[expose] def r91 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 106 * w 107) + (-1 * w 106 * w 109) + (1 * w 107 * w 108) + (1 * w 108 * w 109) + (1 * w 130)

@[expose] def r92 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 110 * w 110) + (2 * w 110 * w 112) + (-2 * w 111 * w 111) + (-4 * w 111 * w 113) + (-1 * w 112 * w 112) + (-2 * w 113 * w 113) + (1 * w 131)

@[expose] def r93 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 110 * w 111) + (-1 * w 110 * w 113) + (1 * w 111 * w 112) + (1 * w 112 * w 113) + (1 * w 132)

@[expose] def r94 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 114 * w 114) + (2 * w 114 * w 116) + (-2 * w 115 * w 115) + (-4 * w 115 * w 117) + (-1 * w 116 * w 116) + (-2 * w 117 * w 117) + (1 * w 133)

@[expose] def r95 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 114 * w 115) + (-1 * w 114 * w 117) + (1 * w 115 * w 116) + (1 * w 116 * w 117) + (1 * w 134)

@[expose] def r96 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 0 * w 0) + ((1 / 7446) * w 0 * w 102) + (-2 * w 0 * w 118) + ((-1 / 221771664) * w 102 * w 102) + ((1 / 7446) * w 102 * w 118) + ((-1 / 110885832) * w 103 * w 103) + (-1 * w 118 * w 118) + (1 * w 135)

@[expose] def r97 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 0 * w 103) + ((1 / 14892) * w 102 * w 103) + (-1 * w 103 * w 118) + (1 * w 136)

@[expose] def r98 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 123 * w 123) + (-8 * w 124 * w 124) + (1 * w 137)

@[expose] def r99 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 123 * w 124) + (1 * w 138)

@[expose] def r100 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 79 * w 82) + (-2 * w 80 * w 83) + (1 * w 139)

@[expose] def r101 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 79 * w 83) + (-1 * w 80 * w 82) + (1 * w 140)

@[expose] def r102 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 85 * w 139) + (-2 * w 86 * w 140) + (1 * w 141)

@[expose] def r103 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 85 * w 140) + (-1 * w 86 * w 139) + (1 * w 142)

@[expose] def r104 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 88 * w 141) + (-2 * w 89 * w 142) + (1 * w 143)

@[expose] def r105 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 88 * w 142) + (-1 * w 89 * w 141) + (1 * w 144)

@[expose] def r106 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 143 * w 143) + (2 * w 144 * w 144) + (1 * w 145)

@[expose] def r107 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 38 * w 146)

@[expose] def r108 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 38 * w 38) + (1 * w 147)

@[expose] def r109 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 38 * w 147) + (1 * w 148)

@[expose] def r110 (S : ℚ) (w : Assignment) : ℚ := ((-1205412 / 3081901) * w 38 * w 147) + (-1 * w 147 * w 147) + ((-1952786 / 3081901) * w 147 * w 148) + (1 * w 149)

@[expose] def r111 (S : ℚ) (w : Assignment) : ℚ := (2 * w 38 * w 38) + (-1 * w 38 * w 147) + (1 * w 150)

@[expose] def r112 (S : ℚ) (w : Assignment) : ℚ := (-1) + (2 * w 38) + ((-16 / 976393) * w 38 * w 151) + (-1 * w 147) + ((76265 / 1952786) * w 147 * w 151) + ((3081901 / 1952786) * w 149 * w 151)

@[expose] def r113 (S : ℚ) (w : Assignment) : ℚ := (3 * w 38 * w 151) + (-1 * w 147 * w 151) + (1 * w 150 * w 151) + (1 * w 152)

@[expose] def r114 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 38 * w 151) + (-1 * w 38 * w 152) + (1 * w 153)

@[expose] def r115 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 151 * w 151) + (-2 * w 151 * w 152) + (-1 * w 152 * w 152) + (1 * w 154)

@[expose] def r116 (S : ℚ) (w : Assignment) : ℚ := (1 * w 38 * w 155) + (-1 * w 154 * w 154) + (-1 * w 155)

@[expose] def r117 (S : ℚ) (w : Assignment) : ℚ := (1 * w 151 * w 156) + (1 * w 152 * w 156) + (-1 * w 153 * w 156) + (-1 * w 155 * w 155)

@[expose] def r118 (S : ℚ) (w : Assignment) : ℚ := (1 * w 151 * w 157) + (-1 * w 156 * w 156)

@[expose] def r119 (S : ℚ) (w : Assignment) : ℚ := (1 * w 151 * w 158) + (-1 * w 157 * w 157)

@[expose] def r120 (S : ℚ) (w : Assignment) : ℚ := (-1) + (-1 * w 126 * w 156) + (1 * w 159)

@[expose] def r121 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 125 * w 151) + (-1 * w 159 * w 159) + (1 * w 160)

@[expose] def r122 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 58 * w 151) + (-1 * w 160 * w 160) + (1 * w 161)

@[expose] def r123 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 59 * w 151) + (1 * w 162)

@[expose] def r124 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 60 * w 151) + (-1 * w 161 * w 161) + (-2 * w 162 * w 162) + (1 * w 163)

@[expose] def r125 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 61 * w 151) + (-2 * w 161 * w 162) + (1 * w 164)

@[expose] def r126 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 62 * w 151) + (-1 * w 163 * w 163) + (-2 * w 164 * w 164) + (1 * w 165)

@[expose] def r127 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 63 * w 151) + (-2 * w 163 * w 164) + (1 * w 166)

@[expose] def r128 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 64 * w 151) + (-1 * w 165 * w 165) + (-2 * w 166 * w 166) + (1 * w 167)

@[expose] def r129 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 65 * w 151) + (-2 * w 165 * w 166) + (1 * w 168)

@[expose] def r130 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 19 * w 151) + (1 * w 151) + (-1 * w 167 * w 167) + (-2 * w 168 * w 168) + (1 * w 169)

@[expose] def r131 (S : ℚ) (w : Assignment) : ℚ := (1 * w 20 * w 151) + (-2 * w 167 * w 168) + (1 * w 170)

@[expose] def r132 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 23 * w 151) + (1 * w 151) + (-1 * w 169 * w 169) + (-2 * w 170 * w 170) + (1 * w 171)

@[expose] def r133 (S : ℚ) (w : Assignment) : ℚ := (1 * w 24 * w 151) + (-2 * w 169 * w 170) + (1 * w 172)

@[expose] def r134 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 27 * w 151) + (1 * w 151) + (-1 * w 171 * w 171) + (-2 * w 172 * w 172) + (1 * w 173)

@[expose] def r135 (S : ℚ) (w : Assignment) : ℚ := (1 * w 28 * w 151) + (-2 * w 171 * w 172) + (1 * w 174)

@[expose] def r136 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 31 * w 151) + (1 * w 151) + (-1 * w 173 * w 173) + (-2 * w 174 * w 174) + (1 * w 175)

@[expose] def r137 (S : ℚ) (w : Assignment) : ℚ := (1 * w 32 * w 151) + (-2 * w 173 * w 174) + (1 * w 176)

@[expose] def r138 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 127 * w 156) + (-1 * w 175 * w 175) + (-2 * w 176 * w 176) + (1 * w 177)

@[expose] def r139 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 128 * w 156) + (-2 * w 175 * w 176) + (1 * w 178)

@[expose] def r140 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 129 * w 158) + (-1 * w 177 * w 177) + (-2 * w 178 * w 178) + (1 * w 179)

@[expose] def r141 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 130 * w 158) + (-2 * w 177 * w 178) + (1 * w 180)

@[expose] def r142 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 131 * w 158) + (-1 * w 179 * w 179) + (-2 * w 180 * w 180) + (1 * w 181)

@[expose] def r143 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 132 * w 158) + (-2 * w 179 * w 180) + (1 * w 182)

@[expose] def r144 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 133 * w 158) + (-1 * w 181 * w 181) + (-2 * w 182 * w 182) + (1 * w 183)

@[expose] def r145 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 134 * w 158) + (-2 * w 181 * w 182) + (1 * w 184)

@[expose] def r146 (S : ℚ) (w : Assignment) : ℚ := (-110885832 * w 0 * w 156) + (7446 * w 102 * w 156) + (-110885832 * w 118 * w 156) + (-221771664 * w 135 * w 156) + (-13860729 * w 156) + (-1 * w 183 * w 183) + (-2 * w 184 * w 184) + (1 * w 185)

@[expose] def r147 (S : ℚ) (w : Assignment) : ℚ := (7446 * w 103 * w 156) + (29784 * w 136 * w 156) + (-2 * w 183 * w 184) + (1 * w 186)

@[expose] def r148 (S : ℚ) (w : Assignment) : ℚ := (2 * w 123 * w 158) + (-1 * w 137 * w 158) + (-1 * w 158) + (-1 * w 185 * w 185) + (-2 * w 186 * w 186) + (1 * w 187)

@[expose] def r149 (S : ℚ) (w : Assignment) : ℚ := (4 * w 124 * w 158) + (-4 * w 138 * w 158) + (-2 * w 185 * w 186) + (1 * w 188)

@[expose] def r150 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 2) * w 187 * w 187) + (1 * w 187 * w 189) + (1 * w 188 * w 188)

@[expose] def r151 (S : ℚ) (w : Assignment) : ℚ := (1 * w 151 * w 190) + (1 * w 152 * w 190) + (-1 * w 153 * w 190) + (-1 * w 189 * w 189)

@[expose] def r152 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 39 * w 190) + (1 * w 191)

@[expose] def r153 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 40 * w 40) + (1 * w 192)

@[expose] def r154 (S : ℚ) (w : Assignment) : ℚ := (3 * w 39 * w 191) + (17 * w 41 * w 41) + (-289 * w 190) + (-34 * w 191)

@[expose] def r155 (S : ℚ) (w : Assignment) : ℚ := (-289 * w 39 * w 39) + (34 * w 39 * w 191) + ((34 / 3) * w 39 * w 192) + (-1 * w 191 * w 191) + ((-2 / 3) * w 191 * w 192) + ((1 / 3) * w 192 * w 192) + (1 * w 193)

@[expose] def r156 (S : ℚ) (w : Assignment) : ℚ := (17 * w 42 * w 42) + (3 * w 190 * w 193)

@[expose] def r157 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 143 * w 143) + (-2 * w 143 * w 145) + (-1 * w 145 * w 145) + (1 * w 146 * w 194)

@[expose] def r158 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 194 * w 194) + (1 * w 195)

@[expose] def r159 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 194 * w 195) + (1 * w 196)

@[expose] def r160 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 194 * w 195) + ((-3081901 / 1205412) * w 195 * w 195) + ((-976393 / 602706) * w 195 * w 196) + (1 * w 197)

@[expose] def r161 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 146 * w 194) + (1 * w 146 * w 195) + (1 * w 198)

@[expose] def r162 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 198 * w 198) + (1 * w 199)

@[expose] def r163 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 199 * w 199) + (1 * w 200)

@[expose] def r164 (S : ℚ) (w : Assignment) : ℚ := ((-16 / 976393) * w 194 * w 201) + ((76265 / 1952786) * w 195 * w 201) + ((602706 / 976393) * w 197 * w 201) + (1 * w 198 * w 200)

@[expose] def r165 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 194 * w 194) + ((1 / 2) * w 194 * w 195) + (1 * w 202)

@[expose] def r166 (S : ℚ) (w : Assignment) : ℚ := (3 * w 194 * w 203) + (-1 * w 195 * w 203) + (-1 * w 201) + (-2 * w 202 * w 203) + (-1 * w 203)

@[expose] def r167 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 194 * w 201) + (1 * w 204)

@[expose] def r168 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 201 * w 201) + (1 * w 205)

@[expose] def r169 (S : ℚ) (w : Assignment) : ℚ := (1 * w 194 * w 206) + (-1 * w 205 * w 205) + (-1 * w 206)

@[expose] def r170 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 201 * w 207) + (1 * w 204 * w 207) + (-1 * w 206 * w 206)

@[expose] def r171 (S : ℚ) (w : Assignment) : ℚ := (1 * w 203 * w 208) + (-1 * w 207 * w 207)

@[expose] def r172 (S : ℚ) (w : Assignment) : ℚ := (1 * w 203 * w 209) + (-1 * w 208 * w 208)

@[expose] def r173 (S : ℚ) (w : Assignment) : ℚ := (-1) + (-1 * w 126 * w 207) + (1 * w 210)

@[expose] def r174 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 125 * w 203) + (-1 * w 210 * w 210) + (1 * w 211)

@[expose] def r175 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 58 * w 203) + (-1 * w 211 * w 211) + (1 * w 212)

@[expose] def r176 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 59 * w 203) + (1 * w 213)

@[expose] def r177 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 60 * w 203) + (-1 * w 212 * w 212) + (-2 * w 213 * w 213) + (1 * w 214)

@[expose] def r178 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 61 * w 203) + (-2 * w 212 * w 213) + (1 * w 215)

@[expose] def r179 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 62 * w 203) + (-1 * w 214 * w 214) + (-2 * w 215 * w 215) + (1 * w 216)

@[expose] def r180 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 63 * w 203) + (-2 * w 214 * w 215) + (1 * w 217)

@[expose] def r181 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 64 * w 203) + (-1 * w 216 * w 216) + (-2 * w 217 * w 217) + (1 * w 218)

@[expose] def r182 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 65 * w 203) + (-2 * w 216 * w 217) + (1 * w 219)

@[expose] def r183 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 19 * w 203) + (1 * w 203) + (-1 * w 218 * w 218) + (-2 * w 219 * w 219) + (1 * w 220)

@[expose] def r184 (S : ℚ) (w : Assignment) : ℚ := (1 * w 20 * w 203) + (-2 * w 218 * w 219) + (1 * w 221)

@[expose] def r185 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 23 * w 203) + (1 * w 203) + (-1 * w 220 * w 220) + (-2 * w 221 * w 221) + (1 * w 222)

@[expose] def r186 (S : ℚ) (w : Assignment) : ℚ := (1 * w 24 * w 203) + (-2 * w 220 * w 221) + (1 * w 223)

@[expose] def r187 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 27 * w 203) + (1 * w 203) + (-1 * w 222 * w 222) + (-2 * w 223 * w 223) + (1 * w 224)

@[expose] def r188 (S : ℚ) (w : Assignment) : ℚ := (1 * w 28 * w 203) + (-2 * w 222 * w 223) + (1 * w 225)

@[expose] def r189 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 31 * w 203) + (1 * w 203) + (-1 * w 224 * w 224) + (-2 * w 225 * w 225) + (1 * w 226)

@[expose] def r190 (S : ℚ) (w : Assignment) : ℚ := (1 * w 32 * w 203) + (-2 * w 224 * w 225) + (1 * w 227)

@[expose] def r191 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 127 * w 207) + (-1 * w 226 * w 226) + (-2 * w 227 * w 227) + (1 * w 228)

@[expose] def r192 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 128 * w 207) + (-2 * w 226 * w 227) + (1 * w 229)

@[expose] def r193 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 129 * w 209) + (-1 * w 228 * w 228) + (-2 * w 229 * w 229) + (1 * w 230)

@[expose] def r194 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 130 * w 209) + (-2 * w 228 * w 229) + (1 * w 231)

@[expose] def r195 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 131 * w 209) + (-1 * w 230 * w 230) + (-2 * w 231 * w 231) + (1 * w 232)

@[expose] def r196 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 132 * w 209) + (-2 * w 230 * w 231) + (1 * w 233)

@[expose] def r197 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 133 * w 209) + (-1 * w 232 * w 232) + (-2 * w 233 * w 233) + (1 * w 234)

@[expose] def r198 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 134 * w 209) + (-2 * w 232 * w 233) + (1 * w 235)

@[expose] def r199 (S : ℚ) (w : Assignment) : ℚ := (-110885832 * w 0 * w 207) + (7446 * w 102 * w 207) + (-110885832 * w 118 * w 207) + (-221771664 * w 135 * w 207) + (-13860729 * w 207) + (-1 * w 234 * w 234) + (-2 * w 235 * w 235) + (1 * w 236)

@[expose] def r200 (S : ℚ) (w : Assignment) : ℚ := (7446 * w 103 * w 207) + (29784 * w 136 * w 207) + (-2 * w 234 * w 235) + (1 * w 237)

@[expose] def r201 (S : ℚ) (w : Assignment) : ℚ := (2 * w 123 * w 209) + (-1 * w 137 * w 209) + (-1 * w 209) + (-1 * w 236 * w 236) + (-2 * w 237 * w 237) + (1 * w 238)

@[expose] def r202 (S : ℚ) (w : Assignment) : ℚ := (4 * w 124 * w 209) + (-4 * w 138 * w 209) + (-2 * w 236 * w 237) + (1 * w 239)

@[expose] def r203 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 2) * w 238 * w 238) + (1 * w 238 * w 240) + (1 * w 239 * w 239)

@[expose] def r204 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 201 * w 241) + (1 * w 204 * w 241) + (-1 * w 240 * w 240)

@[expose] def r205 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 43 * w 241) + (1 * w 242)

@[expose] def r206 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 44 * w 44) + (1 * w 243)

@[expose] def r207 (S : ℚ) (w : Assignment) : ℚ := (3 * w 43 * w 242) + (17 * w 45 * w 45) + (-289 * w 241) + (-34 * w 242)

@[expose] def r208 (S : ℚ) (w : Assignment) : ℚ := (-289 * w 43 * w 43) + (34 * w 43 * w 242) + ((34 / 3) * w 43 * w 243) + (-1 * w 242 * w 242) + ((-2 / 3) * w 242 * w 243) + ((1 / 3) * w 243 * w 243) + (1 * w 244)

@[expose] def r209 (S : ℚ) (w : Assignment) : ℚ := (17 * w 46 * w 46) + (3 * w 241 * w 244)

@[expose] def r210 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 145 * w 145) + (1 * w 146 * w 245)

@[expose] def r211 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 245 * w 245) + (1 * w 246)

@[expose] def r212 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 245 * w 246) + (1 * w 247)

@[expose] def r213 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 245 * w 246) + ((-3081901 / 1205412) * w 246 * w 246) + ((-976393 / 602706) * w 246 * w 247) + (1 * w 248)

@[expose] def r214 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 146 * w 245) + (1 * w 146 * w 246) + (1 * w 249)

@[expose] def r215 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 249 * w 249) + (1 * w 250)

@[expose] def r216 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 250 * w 250) + (1 * w 251)

@[expose] def r217 (S : ℚ) (w : Assignment) : ℚ := ((-16 / 976393) * w 245 * w 252) + ((76265 / 1952786) * w 246 * w 252) + ((602706 / 976393) * w 248 * w 252) + (1 * w 249 * w 251)

@[expose] def r218 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 245 * w 245) + ((1 / 2) * w 245 * w 246) + (1 * w 253)

@[expose] def r219 (S : ℚ) (w : Assignment) : ℚ := (3 * w 245 * w 254) + (-1 * w 246 * w 254) + (-1 * w 252) + (-2 * w 253 * w 254) + (-1 * w 254)

@[expose] def r220 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 245 * w 252) + (1 * w 255)

@[expose] def r221 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 252 * w 252) + (1 * w 256)

@[expose] def r222 (S : ℚ) (w : Assignment) : ℚ := (1 * w 245 * w 257) + (-1 * w 256 * w 256) + (-1 * w 257)

@[expose] def r223 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 252 * w 258) + (1 * w 255 * w 258) + (-1 * w 257 * w 257)

@[expose] def r224 (S : ℚ) (w : Assignment) : ℚ := (1 * w 254 * w 259) + (-1 * w 258 * w 258)

@[expose] def r225 (S : ℚ) (w : Assignment) : ℚ := (1 * w 254 * w 260) + (-1 * w 259 * w 259)

@[expose] def r226 (S : ℚ) (w : Assignment) : ℚ := (-1) + (-1 * w 126 * w 258) + (1 * w 261)

@[expose] def r227 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 125 * w 254) + (-1 * w 261 * w 261) + (1 * w 262)

@[expose] def r228 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 58 * w 254) + (-1 * w 262 * w 262) + (1 * w 263)

@[expose] def r229 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 59 * w 254) + (1 * w 264)

@[expose] def r230 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 60 * w 254) + (-1 * w 263 * w 263) + (-2 * w 264 * w 264) + (1 * w 265)

@[expose] def r231 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 61 * w 254) + (-2 * w 263 * w 264) + (1 * w 266)

@[expose] def r232 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 62 * w 254) + (-1 * w 265 * w 265) + (-2 * w 266 * w 266) + (1 * w 267)

@[expose] def r233 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 63 * w 254) + (-2 * w 265 * w 266) + (1 * w 268)

@[expose] def r234 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 64 * w 254) + (-1 * w 267 * w 267) + (-2 * w 268 * w 268) + (1 * w 269)

@[expose] def r235 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 65 * w 254) + (-2 * w 267 * w 268) + (1 * w 270)

@[expose] def r236 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 19 * w 254) + (1 * w 254) + (-1 * w 269 * w 269) + (-2 * w 270 * w 270) + (1 * w 271)

@[expose] def r237 (S : ℚ) (w : Assignment) : ℚ := (1 * w 20 * w 254) + (-2 * w 269 * w 270) + (1 * w 272)

@[expose] def r238 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 23 * w 254) + (1 * w 254) + (-1 * w 271 * w 271) + (-2 * w 272 * w 272) + (1 * w 273)

@[expose] def r239 (S : ℚ) (w : Assignment) : ℚ := (1 * w 24 * w 254) + (-2 * w 271 * w 272) + (1 * w 274)

@[expose] def r240 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 27 * w 254) + (1 * w 254) + (-1 * w 273 * w 273) + (-2 * w 274 * w 274) + (1 * w 275)

@[expose] def r241 (S : ℚ) (w : Assignment) : ℚ := (1 * w 28 * w 254) + (-2 * w 273 * w 274) + (1 * w 276)

@[expose] def r242 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 31 * w 254) + (1 * w 254) + (-1 * w 275 * w 275) + (-2 * w 276 * w 276) + (1 * w 277)

@[expose] def r243 (S : ℚ) (w : Assignment) : ℚ := (1 * w 32 * w 254) + (-2 * w 275 * w 276) + (1 * w 278)

@[expose] def r244 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 127 * w 258) + (-1 * w 277 * w 277) + (-2 * w 278 * w 278) + (1 * w 279)

@[expose] def r245 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 128 * w 258) + (-2 * w 277 * w 278) + (1 * w 280)

@[expose] def r246 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 129 * w 260) + (-1 * w 279 * w 279) + (-2 * w 280 * w 280) + (1 * w 281)

@[expose] def r247 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 130 * w 260) + (-2 * w 279 * w 280) + (1 * w 282)

@[expose] def r248 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 131 * w 260) + (-1 * w 281 * w 281) + (-2 * w 282 * w 282) + (1 * w 283)

@[expose] def r249 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 132 * w 260) + (-2 * w 281 * w 282) + (1 * w 284)

@[expose] def r250 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 133 * w 260) + (-1 * w 283 * w 283) + (-2 * w 284 * w 284) + (1 * w 285)

@[expose] def r251 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 134 * w 260) + (-2 * w 283 * w 284) + (1 * w 286)

@[expose] def r252 (S : ℚ) (w : Assignment) : ℚ := (-110885832 * w 0 * w 258) + (7446 * w 102 * w 258) + (-110885832 * w 118 * w 258) + (-221771664 * w 135 * w 258) + (-13860729 * w 258) + (-1 * w 285 * w 285) + (-2 * w 286 * w 286) + (1 * w 287)

@[expose] def r253 (S : ℚ) (w : Assignment) : ℚ := (7446 * w 103 * w 258) + (29784 * w 136 * w 258) + (-2 * w 285 * w 286) + (1 * w 288)

@[expose] def r254 (S : ℚ) (w : Assignment) : ℚ := (2 * w 123 * w 260) + (-1 * w 137 * w 260) + (-1 * w 260) + (-1 * w 287 * w 287) + (-2 * w 288 * w 288) + (1 * w 289)

@[expose] def r255 (S : ℚ) (w : Assignment) : ℚ := (4 * w 124 * w 260) + (-4 * w 138 * w 260) + (-2 * w 287 * w 288) + (1 * w 290)

@[expose] def r256 (S : ℚ) (w : Assignment) : ℚ := ((-1 / 2) * w 289 * w 289) + (1 * w 289 * w 291) + (1 * w 290 * w 290)

@[expose] def r257 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 252 * w 292) + (1 * w 255 * w 292) + (-1 * w 291 * w 291)

@[expose] def r258 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 47 * w 292) + (1 * w 293)

@[expose] def r259 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 48 * w 48) + (1 * w 294)

@[expose] def r260 (S : ℚ) (w : Assignment) : ℚ := (3 * w 47 * w 293) + (17 * w 49 * w 49) + (-289 * w 292) + (-34 * w 293)

@[expose] def r261 (S : ℚ) (w : Assignment) : ℚ := (-289 * w 47 * w 47) + (34 * w 47 * w 293) + ((34 / 3) * w 47 * w 294) + (-1 * w 293 * w 293) + ((-2 / 3) * w 293 * w 294) + ((1 / 3) * w 294 * w 294) + (1 * w 295)

@[expose] def r262 (S : ℚ) (w : Assignment) : ℚ := (17 * w 50 * w 50) + (3 * w 292 * w 295)

@[expose] def r263 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 0 * w 0) + (-2 * w 0 * w 118) + (-1 * w 118 * w 118) + (1 * w 296)

@[expose] def r264 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 0 * w 0) + (-2 * w 0 * w 118) + ((-496408687 / 100291113) * w 0 * w 296) + (-1 * w 118 * w 118) + ((-496408687 / 100291113) * w 118 * w 296) + ((-197130368 / 33430371) * w 296 * w 296) + (1 * w 297)

@[expose] def r265 (S : ℚ) (w : Assignment) : ℚ := (-1) + (101783690143177584 * w 0 * w 298) + (101783690143177584 * w 118 * w 298) + (267108917866935984 * w 296 * w 298) + (533801448346128768 * w 297 * w 298) + (4376874610839020 * w 298)

@[expose] def r266 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 298 * w 298) + (1 * w 299)

@[expose] def r267 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 299 * w 299) + (1 * w 300)

@[expose] def r268 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 300 * w 300) + (1 * w 301)

@[expose] def r269 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 301 * w 301) + (1 * w 302)

@[expose] def r270 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 82 * w 303) + (-2 * w 83 * w 304) + (1 * w 305)

@[expose] def r271 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 82 * w 304) + (-1 * w 83 * w 303) + (1 * w 306)

@[expose] def r272 (S : ℚ) (w : Assignment) : ℚ := (-11) + ((-57 / 8) * w 82 * w 82) + (14 * w 82 * w 83) + ((-57 / 4) * w 83 * w 83) + ((-57 / 8) * w 303 * w 303) + (14 * w 303 * w 304) + ((-57 / 4) * w 304 * w 304) + ((-39 / 4) * w 305) + (1 * w 305 * w 305) + (18 * w 306) + (2 * w 306 * w 306)

@[expose] def r273 (S : ℚ) (w : Assignment) : ℚ := (6) + ((7 / 2) * w 82 * w 82) + ((-57 / 4) * w 82 * w 83) + (7 * w 83 * w 83) + ((7 / 2) * w 303 * w 303) + ((-57 / 4) * w 303 * w 304) + (7 * w 304 * w 304) + (9 * w 305) + (2 * w 305 * w 306) + ((-39 / 4) * w 306)

@[expose] def r274 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 303 * w 303) + (2 * w 304 * w 304) + (1 * w 307)

@[expose] def r275 (S : ℚ) (w : Assignment) : ℚ := (-1) + (1 * w 307 * w 308)

@[expose] def r276 (S : ℚ) (w : Assignment) : ℚ := (101783690143177584 * w 0 * w 309) + (-1 * w 37) + (101783690143177584 * w 118 * w 309) + (267108917866935984 * w 296 * w 309) + (533801448346128768 * w 297 * w 309) + (4376874610839020 * w 309)

@[expose] def r277 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 302 * w 308) + (1 * w 309 * w 310)

@[expose] def r278 (S : ℚ) (w : Assignment) : ℚ := (-2 * w 33 * w 298) + (-1 * w 309 * w 309) + (1 * w 311)

@[expose] def r279 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 310 * w 310) + (1 * w 312)

@[expose] def r280 (S : ℚ) (w : Assignment) : ℚ := (-1) + (-101783690143177584 * w 0 * w 312) + (11648532634745815423296 * w 0 * w 313) + (-101783690143177584 * w 118 * w 312) + (11648532634745815423296 * w 118 * w 313) + (-267108917866935984 * w 296 * w 312) + (30569012996363621752896 * w 296 * w 313) + (-533801448346128768 * w 297 * w 312) + (61090372954524360724992 * w 297 * w 313) + (-2 * w 311) + (-1 * w 311 * w 311) + (-4376874610839020 * w 312) + (500907037962860804881 * w 313)

@[expose] def r281 (S : ℚ) (w : Assignment) : ℚ := (1 * w 298 * w 314) + (-114444 * w 313 * w 313)

@[expose] def r282 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 51 * w 314) + (1 * w 315)

@[expose] def r283 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 52 * w 52) + (1 * w 316)

@[expose] def r284 (S : ℚ) (w : Assignment) : ℚ := (-289 * w 51 * w 51) + (34 * w 51 * w 315) + ((34 / 3) * w 51 * w 316) + (-1 * w 315 * w 315) + ((-2 / 3) * w 315 * w 316) + ((1 / 3) * w 316 * w 316) + (1 * w 317)

@[expose] def r285 (S : ℚ) (w : Assignment) : ℚ := (3 * w 51 * w 315) + (17 * w 53 * w 53) + (-289 * w 314) + (-34 * w 315)

@[expose] def r286 (S : ℚ) (w : Assignment) : ℚ := (17 * w 54 * w 54) + (3 * w 314 * w 317)

@[expose] def r287 (S : ℚ) (w : Assignment) : ℚ := (2 * S^2) + (1 * w 55 * w 55) + (6 * w 56 * w 56) + (-2 * w 57 * w 57) + (-50331648 * w 145 * w 145 * S^2) + (-24576 * w 145 * w 308 * S^1) + (-3 * w 308 * w 308)

@[expose] def stage0 (S : ℚ) : List Row := [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S, r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S, r120 S, r121 S, r122 S, r123 S, r124 S, r125 S, r126 S, r127 S, r128 S, r129 S, r130 S, r131 S, r132 S, r133 S, r134 S, r135 S, r136 S, r137 S, r138 S, r139 S, r140 S, r141 S, r142 S, r143 S, r144 S, r145 S, r146 S, r147 S, r148 S, r149 S, r150 S, r151 S, r152 S, r153 S, r154 S, r155 S, r156 S, r157 S, r158 S, r159 S, r160 S, r161 S, r162 S, r163 S, r164 S, r165 S, r166 S, r167 S, r168 S, r169 S, r170 S, r171 S, r172 S, r173 S, r174 S, r175 S, r176 S, r177 S, r178 S, r179 S, r180 S, r181 S, r182 S, r183 S, r184 S, r185 S, r186 S, r187 S, r188 S, r189 S, r190 S, r191 S, r192 S, r193 S, r194 S, r195 S, r196 S, r197 S, r198 S, r199 S, r200 S, r201 S, r202 S, r203 S, r204 S, r205 S, r206 S, r207 S, r208 S, r209 S, r210 S, r211 S, r212 S, r213 S, r214 S, r215 S, r216 S, r217 S, r218 S, r219 S, r220 S, r221 S, r222 S, r223 S, r224 S, r225 S, r226 S, r227 S, r228 S, r229 S, r230 S, r231 S, r232 S, r233 S, r234 S, r235 S, r236 S, r237 S, r238 S, r239 S, r240 S, r241 S, r242 S, r243 S, r244 S, r245 S, r246 S, r247 S, r248 S, r249 S, r250 S, r251 S, r252 S, r253 S, r254 S, r255 S, r256 S, r257 S, r258 S, r259 S, r260 S, r261 S, r262 S, r263 S, r264 S, r265 S, r266 S, r267 S, r268 S, r269 S, r270 S, r271 S, r272 S, r273 S, r274 S, r275 S, r276 S, r277 S, r278 S, r279 S, r280 S, r281 S, r282 S, r283 S, r284 S, r285 S, r286 S, r287 S]

@[expose] def r288 (S : ℚ) (w : Assignment) : ℚ := (32 * S^2) + (16 * w 55 * w 55) + (96 * w 56 * w 56) + (-32 * w 57 * w 57) + (-805306368 * w 145 * w 145 * S^2) + (-393216 * w 145 * w 308 * S^1) + (-48 * w 308 * w 308)

@[expose] def stage1 (S : ℚ) : List Row := [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S, r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S, r120 S, r121 S, r122 S, r123 S, r124 S, r125 S, r126 S, r127 S, r128 S, r129 S, r130 S, r131 S, r132 S, r133 S, r134 S, r135 S, r136 S, r137 S, r138 S, r139 S, r140 S, r141 S, r142 S, r143 S, r144 S, r145 S, r146 S, r147 S, r148 S, r149 S, r150 S, r151 S, r152 S, r153 S, r154 S, r155 S, r156 S, r157 S, r158 S, r159 S, r160 S, r161 S, r162 S, r163 S, r164 S, r165 S, r166 S, r167 S, r168 S, r169 S, r170 S, r171 S, r172 S, r173 S, r174 S, r175 S, r176 S, r177 S, r178 S, r179 S, r180 S, r181 S, r182 S, r183 S, r184 S, r185 S, r186 S, r187 S, r188 S, r189 S, r190 S, r191 S, r192 S, r193 S, r194 S, r195 S, r196 S, r197 S, r198 S, r199 S, r200 S, r201 S, r202 S, r203 S, r204 S, r205 S, r206 S, r207 S, r208 S, r209 S, r210 S, r211 S, r212 S, r213 S, r214 S, r215 S, r216 S, r217 S, r218 S, r219 S, r220 S, r221 S, r222 S, r223 S, r224 S, r225 S, r226 S, r227 S, r228 S, r229 S, r230 S, r231 S, r232 S, r233 S, r234 S, r235 S, r236 S, r237 S, r238 S, r239 S, r240 S, r241 S, r242 S, r243 S, r244 S, r245 S, r246 S, r247 S, r248 S, r249 S, r250 S, r251 S, r252 S, r253 S, r254 S, r255 S, r256 S, r257 S, r258 S, r259 S, r260 S, r261 S, r262 S, r263 S, r264 S, r265 S, r266 S, r267 S, r268 S, r269 S, r270 S, r271 S, r272 S, r273 S, r274 S, r275 S, r276 S, r277 S, r278 S, r279 S, r280 S, r281 S, r282 S, r283 S, r284 S, r285 S, r286 S, r288 S]

@[expose] def r289 (S : ℚ) (w : Assignment) : ℚ := (8 * w 55 * S^1) + (1 * w 55 * w 55) + (-6 * w 55 * w 56) + (6 * w 55 * w 57) + (15 * w 56 * w 56) + (-18 * w 56 * w 57) + (7 * w 57 * w 57) + (-805306368 * w 145 * w 145 * S^2) + (-393216 * w 145 * w 308 * S^1) + (-48 * w 308 * w 308)

@[expose] def stage2 (S : ℚ) : List Row := [r0 S, r1 S, r2 S, r3 S, r4 S, r5 S, r6 S, r7 S, r8 S, r9 S, r10 S, r11 S, r12 S, r13 S, r14 S, r15 S, r16 S, r17 S, r18 S, r19 S, r20 S, r21 S, r22 S, r23 S, r24 S, r25 S, r26 S, r27 S, r28 S, r29 S, r30 S, r31 S, r32 S, r33 S, r34 S, r35 S, r36 S, r37 S, r38 S, r39 S, r40 S, r41 S, r42 S, r43 S, r44 S, r45 S, r46 S, r47 S, r48 S, r49 S, r50 S, r51 S, r52 S, r53 S, r54 S, r55 S, r56 S, r57 S, r58 S, r59 S, r60 S, r61 S, r62 S, r63 S, r64 S, r65 S, r66 S, r67 S, r68 S, r69 S, r70 S, r71 S, r72 S, r73 S, r74 S, r75 S, r76 S, r77 S, r78 S, r79 S, r80 S, r81 S, r82 S, r83 S, r84 S, r85 S, r86 S, r87 S, r88 S, r89 S, r90 S, r91 S, r92 S, r93 S, r94 S, r95 S, r96 S, r97 S, r98 S, r99 S, r100 S, r101 S, r102 S, r103 S, r104 S, r105 S, r106 S, r107 S, r108 S, r109 S, r110 S, r111 S, r112 S, r113 S, r114 S, r115 S, r116 S, r117 S, r118 S, r119 S, r120 S, r121 S, r122 S, r123 S, r124 S, r125 S, r126 S, r127 S, r128 S, r129 S, r130 S, r131 S, r132 S, r133 S, r134 S, r135 S, r136 S, r137 S, r138 S, r139 S, r140 S, r141 S, r142 S, r143 S, r144 S, r145 S, r146 S, r147 S, r148 S, r149 S, r150 S, r151 S, r152 S, r153 S, r154 S, r155 S, r156 S, r157 S, r158 S, r159 S, r160 S, r161 S, r162 S, r163 S, r164 S, r165 S, r166 S, r167 S, r168 S, r169 S, r170 S, r171 S, r172 S, r173 S, r174 S, r175 S, r176 S, r177 S, r178 S, r179 S, r180 S, r181 S, r182 S, r183 S, r184 S, r185 S, r186 S, r187 S, r188 S, r189 S, r190 S, r191 S, r192 S, r193 S, r194 S, r195 S, r196 S, r197 S, r198 S, r199 S, r200 S, r201 S, r202 S, r203 S, r204 S, r205 S, r206 S, r207 S, r208 S, r209 S, r210 S, r211 S, r212 S, r213 S, r214 S, r215 S, r216 S, r217 S, r218 S, r219 S, r220 S, r221 S, r222 S, r223 S, r224 S, r225 S, r226 S, r227 S, r228 S, r229 S, r230 S, r231 S, r232 S, r233 S, r234 S, r235 S, r236 S, r237 S, r238 S, r239 S, r240 S, r241 S, r242 S, r243 S, r244 S, r245 S, r246 S, r247 S, r248 S, r249 S, r250 S, r251 S, r252 S, r253 S, r254 S, r255 S, r256 S, r257 S, r258 S, r259 S, r260 S, r261 S, r262 S, r263 S, r264 S, r265 S, r266 S, r267 S, r268 S, r269 S, r270 S, r271 S, r272 S, r273 S, r274 S, r275 S, r276 S, r277 S, r278 S, r279 S, r280 S, r281 S, r282 S, r283 S, r284 S, r285 S, r286 S, r289 S]

@[expose] def r290 (S : ℚ) (w : Assignment) : ℚ := (1 * w 1 * w 1) + (2 * w 2 * w 2) + (-1 * w 58)

@[expose] def r291 (S : ℚ) (w : Assignment) : ℚ := (1 * w 1 * w 2) + (-1 * w 59)

@[expose] def r292 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 3 * w 3) + (-2 * w 4 * w 4) + (-11 * w 58 * w 58) + (48 * w 58 * w 59) + (-88 * w 59 * w 59)

@[expose] def r293 (S : ℚ) (w : Assignment) : ℚ := (1 * w 3 * w 4) + (-3 * w 58 * w 58) + (22 * w 58 * w 59) + (-24 * w 59 * w 59)

@[expose] def r294 (S : ℚ) (w : Assignment) : ℚ := (1 * w 5 * w 5) + (2 * w 6 * w 6) + (-1 * w 60)

@[expose] def r295 (S : ℚ) (w : Assignment) : ℚ := (1 * w 5 * w 6) + (-1 * w 61)

@[expose] def r296 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 7 * w 7) + (-2 * w 8 * w 8) + (-11 * w 60 * w 60) + (48 * w 60 * w 61) + (-88 * w 61 * w 61)

@[expose] def r297 (S : ℚ) (w : Assignment) : ℚ := (1 * w 7 * w 8) + (-3 * w 60 * w 60) + (22 * w 60 * w 61) + (-24 * w 61 * w 61)

@[expose] def r298 (S : ℚ) (w : Assignment) : ℚ := (1 * w 9 * w 9) + (2 * w 10 * w 10) + (-2 * w 62)

@[expose] def r299 (S : ℚ) (w : Assignment) : ℚ := (1 * w 9 * w 10) + (-1 * w 63)

@[expose] def r300 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 11 * w 11) + (-2 * w 12 * w 12) + (-44 * w 62 * w 62) + (96 * w 62 * w 63) + (-88 * w 63 * w 63)

@[expose] def r301 (S : ℚ) (w : Assignment) : ℚ := (1 * w 11 * w 12) + (-12 * w 62 * w 62) + (44 * w 62 * w 63) + (-24 * w 63 * w 63)

@[expose] def r302 (S : ℚ) (w : Assignment) : ℚ := (1 * w 13 * w 13) + (2 * w 14 * w 14) + (-1 * w 64)

@[expose] def r303 (S : ℚ) (w : Assignment) : ℚ := (1 * w 13 * w 14) + (-1 * w 65)

@[expose] def r304 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 15 * w 15) + (-2 * w 16 * w 16) + (-11 * w 64 * w 64) + (48 * w 64 * w 65) + (-88 * w 65 * w 65)

@[expose] def r305 (S : ℚ) (w : Assignment) : ℚ := (1 * w 15 * w 16) + (-3 * w 64 * w 64) + (22 * w 64 * w 65) + (-24 * w 65 * w 65)

@[expose] def r306 (S : ℚ) (w : Assignment) : ℚ := (1 * w 17 * w 17) + (2 * w 18 * w 18) + (-1 * w 66)

@[expose] def r307 (S : ℚ) (w : Assignment) : ℚ := (1 * w 17 * w 18) + (-1 * w 67)

@[expose] def r308 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 19 * w 19) + (-2 * w 20 * w 20) + (-11 * w 66 * w 66) + (48 * w 66 * w 67) + (-88 * w 67 * w 67)

@[expose] def r309 (S : ℚ) (w : Assignment) : ℚ := (1 * w 19 * w 20) + (-3 * w 66 * w 66) + (22 * w 66 * w 67) + (-24 * w 67 * w 67)

@[expose] def r310 (S : ℚ) (w : Assignment) : ℚ := (1 * w 21 * w 21) + (2 * w 22 * w 22) + (-1 * w 68)

@[expose] def r311 (S : ℚ) (w : Assignment) : ℚ := (1 * w 21 * w 22) + (-1 * w 69)

@[expose] def r312 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 23 * w 23) + (-2 * w 24 * w 24) + (-11 * w 68 * w 68) + (48 * w 68 * w 69) + (-88 * w 69 * w 69)

@[expose] def r313 (S : ℚ) (w : Assignment) : ℚ := (1 * w 23 * w 24) + (-3 * w 68 * w 68) + (22 * w 68 * w 69) + (-24 * w 69 * w 69)

@[expose] def r314 (S : ℚ) (w : Assignment) : ℚ := (1 * w 25 * w 25) + (2 * w 26 * w 26) + (-1 * w 70)

@[expose] def r315 (S : ℚ) (w : Assignment) : ℚ := (1 * w 25 * w 26) + (-1 * w 71)

@[expose] def r316 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 27 * w 27) + (-2 * w 28 * w 28) + (-11 * w 70 * w 70) + (48 * w 70 * w 71) + (-88 * w 71 * w 71)

@[expose] def r317 (S : ℚ) (w : Assignment) : ℚ := (1 * w 27 * w 28) + (-3 * w 70 * w 70) + (22 * w 70 * w 71) + (-24 * w 71 * w 71)

@[expose] def r318 (S : ℚ) (w : Assignment) : ℚ := (1 * w 29 * w 29) + (2 * w 30 * w 30) + (-1 * w 72)

@[expose] def r319 (S : ℚ) (w : Assignment) : ℚ := (1 * w 29 * w 30) + (-1 * w 73)

@[expose] def r320 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 31 * w 31) + (-2 * w 32 * w 32) + (-11 * w 72 * w 72) + (48 * w 72 * w 73) + (-88 * w 73 * w 73)

@[expose] def r321 (S : ℚ) (w : Assignment) : ℚ := (1 * w 31 * w 32) + (-3 * w 72 * w 72) + (22 * w 72 * w 73) + (-24 * w 73 * w 73)

@[expose] def r322 (S : ℚ) (w : Assignment) : ℚ := (1 * w 33 * w 35) + (2 * w 34 * w 36) + (-1 * w 74)

@[expose] def r323 (S : ℚ) (w : Assignment) : ℚ := (1 * w 33 * w 36) + (1 * w 34 * w 35) + (-1 * w 75)

@[expose] def r324 (S : ℚ) (w : Assignment) : ℚ := (1 * w 35 * w 74) + (2 * w 36 * w 75) + (-1 * w 76)

@[expose] def r325 (S : ℚ) (w : Assignment) : ℚ := (1 * w 35 * w 75) + (1 * w 36 * w 74) + (-1 * w 77)

@[expose] def r326 (S : ℚ) (w : Assignment) : ℚ := (8) + (-57 * w 33) + (56 * w 34) + (-78 * w 74) + (-88 * w 74 * w 74) + (192 * w 74 * w 75) + (144 * w 75) + (-176 * w 75 * w 75) + (-57 * w 76) + (56 * w 77)

@[expose] def r327 (S : ℚ) (w : Assignment) : ℚ := (28 * w 33) + (-57 * w 34) + (72 * w 74) + (48 * w 74 * w 74) + (-176 * w 74 * w 75) + (-78 * w 75) + (96 * w 75 * w 75) + (28 * w 76) + (-57 * w 77)

@[expose] def r328 (S : ℚ) (w : Assignment) : ℚ := (1 * w 33 * w 33) + (-2 * w 34 * w 34) + (-1 * w 37 * w 37)

@[expose] def r329 (S : ℚ) (w : Assignment) : ℚ := (1) + (1 * w 58 * w 78) + (-1 * w 66 * w 78)

@[expose] def r330 (S : ℚ) (w : Assignment) : ℚ := (1 * w 1 * w 19) + (2 * w 2 * w 20) + (1 * w 3 * w 17) + (2 * w 4 * w 18) + (1 * w 58 * w 79) + (4 * w 59 * w 80) + (-1 * w 66 * w 79) + (-4 * w 67 * w 80)

@[expose] def r331 (S : ℚ) (w : Assignment) : ℚ := (1 * w 1 * w 20) + (1 * w 2 * w 19) + (1 * w 3 * w 18) + (1 * w 4 * w 17) + (1 * w 58 * w 80) + (2 * w 59 * w 79) + (-1 * w 66 * w 80) + (-2 * w 67 * w 79)

@[expose] def r332 (S : ℚ) (w : Assignment) : ℚ := (1) + (1 * w 60 * w 81) + (-1 * w 68 * w 81)

@[expose] def r333 (S : ℚ) (w : Assignment) : ℚ := (1 * w 5 * w 23) + (2 * w 6 * w 24) + (1 * w 7 * w 21) + (2 * w 8 * w 22) + (1 * w 60 * w 82) + (4 * w 61 * w 83) + (-1 * w 68 * w 82) + (-4 * w 69 * w 83)

@[expose] def r334 (S : ℚ) (w : Assignment) : ℚ := (1 * w 5 * w 24) + (1 * w 6 * w 23) + (1 * w 7 * w 22) + (1 * w 8 * w 21) + (1 * w 60 * w 83) + (2 * w 61 * w 82) + (-1 * w 68 * w 83) + (-2 * w 69 * w 82)

@[expose] def r335 (S : ℚ) (w : Assignment) : ℚ := (1) + (2 * w 62 * w 84) + (-1 * w 70 * w 84)

@[expose] def r336 (S : ℚ) (w : Assignment) : ℚ := (1 * w 9 * w 27) + (2 * w 10 * w 28) + (1 * w 11 * w 25) + (2 * w 12 * w 26) + (2 * w 62 * w 85) + (4 * w 63 * w 86) + (-1 * w 70 * w 85) + (-4 * w 71 * w 86)

@[expose] def r337 (S : ℚ) (w : Assignment) : ℚ := (1 * w 9 * w 28) + (1 * w 10 * w 27) + (1 * w 11 * w 26) + (1 * w 12 * w 25) + (2 * w 62 * w 86) + (2 * w 63 * w 85) + (-1 * w 70 * w 86) + (-2 * w 71 * w 85)

@[expose] def r338 (S : ℚ) (w : Assignment) : ℚ := (1) + (1 * w 64 * w 87) + (-1 * w 72 * w 87)

@[expose] def r339 (S : ℚ) (w : Assignment) : ℚ := (1 * w 13 * w 31) + (2 * w 14 * w 32) + (1 * w 15 * w 29) + (2 * w 16 * w 30) + (1 * w 64 * w 88) + (4 * w 65 * w 89) + (-1 * w 72 * w 88) + (-4 * w 73 * w 89)

@[expose] def r340 (S : ℚ) (w : Assignment) : ℚ := (1 * w 13 * w 32) + (1 * w 14 * w 31) + (1 * w 15 * w 30) + (1 * w 16 * w 29) + (1 * w 64 * w 89) + (2 * w 65 * w 88) + (-1 * w 72 * w 89) + (-2 * w 73 * w 88)

@[expose] def r341 (S : ℚ) (w : Assignment) : ℚ := (1 * w 76 * w 76) + (2 * w 77 * w 77) + (-1 * w 90)

@[expose] def r342 (S : ℚ) (w : Assignment) : ℚ := (1 * w 76 * w 77) + (-1 * w 91)

@[expose] def r343 (S : ℚ) (w : Assignment) : ℚ := (195) + (-2013 * w 90) + (3088 * w 90 * w 90) + (-16896 * w 90 * w 91) + (1155 * w 90 * w 92) + (-1260 * w 90 * w 93) + (4392 * w 91) + (24704 * w 91 * w 91) + (-2520 * w 91 * w 92) + (4620 * w 91 * w 93) + (-195 * w 92)

@[expose] def r344 (S : ℚ) (w : Assignment) : ℚ := (1098 * w 90) + (-2112 * w 90 * w 90) + (12352 * w 90 * w 91) + (-630 * w 90 * w 92) + (1155 * w 90 * w 93) + (-4026 * w 91) + (-16896 * w 91 * w 91) + (2310 * w 91 * w 92) + (-2520 * w 91 * w 93) + (-195 * w 93)

@[expose] def r345 (S : ℚ) (w : Assignment) : ℚ := (8 * w 35 * w 92) + (-28 * w 35 * w 93) + (39 * w 35 * w 94) + (-72 * w 35 * w 95) + (-28 * w 36 * w 92) + (16 * w 36 * w 93) + (-72 * w 36 * w 94) + (78 * w 36 * w 95) + (88 * w 76 * w 94) + (-96 * w 76 * w 95) + (-96 * w 77 * w 94) + (176 * w 77 * w 95) + (57 * w 94) + (-56 * w 95)

@[expose] def r346 (S : ℚ) (w : Assignment) : ℚ := (14 * w 35 * w 92) + (-8 * w 35 * w 93) + (36 * w 35 * w 94) + (-39 * w 35 * w 95) + (-8 * w 36 * w 92) + (28 * w 36 * w 93) + (-39 * w 36 * w 94) + (72 * w 36 * w 95) + (48 * w 76 * w 94) + (-88 * w 76 * w 95) + (-88 * w 77 * w 94) + (96 * w 77 * w 95) + (28 * w 94) + (-57 * w 95)

@[expose] def r347 (S : ℚ) (w : Assignment) : ℚ := (157) + (40 * w 23) + (-2 * w 23 * w 23) + (-75 * w 23 * w 96) + (-4 * w 24 * w 24) + (-150 * w 24 * w 97) + (-120 * w 96)

@[expose] def r348 (S : ℚ) (w : Assignment) : ℚ := (4 * w 23 * w 24) + (75 * w 23 * w 97) + (-40 * w 24) + (75 * w 24 * w 96) + (120 * w 97)

@[expose] def r349 (S : ℚ) (w : Assignment) : ℚ := (157) + (40 * w 27) + (-2 * w 27 * w 27) + (-75 * w 27 * w 98) + (-4 * w 28 * w 28) + (-150 * w 28 * w 99) + (-120 * w 98)

@[expose] def r350 (S : ℚ) (w : Assignment) : ℚ := (4 * w 27 * w 28) + (75 * w 27 * w 99) + (-40 * w 28) + (75 * w 28 * w 98) + (120 * w 99)

@[expose] def r351 (S : ℚ) (w : Assignment) : ℚ := (157) + (40 * w 31) + (-2 * w 31 * w 31) + (-75 * w 31 * w 100) + (-4 * w 32 * w 32) + (-150 * w 32 * w 101) + (-120 * w 100)

@[expose] def r352 (S : ℚ) (w : Assignment) : ℚ := (4 * w 31 * w 32) + (75 * w 31 * w 101) + (-40 * w 32) + (75 * w 32 * w 100) + (120 * w 101)

@[expose] def r353 (S : ℚ) (w : Assignment) : ℚ := (39 * w 1) + (57 * w 1 * w 35) + (-56 * w 1 * w 36) + (88 * w 1 * w 74) + (-96 * w 1 * w 75) + (-72 * w 2) + (-56 * w 2 * w 35) + (114 * w 2 * w 36) + (-96 * w 2 * w 74) + (176 * w 2 * w 75) + (8 * w 3 * w 102) + (-28 * w 3 * w 103) + (-28 * w 4 * w 102) + (16 * w 4 * w 103)

@[expose] def r354 (S : ℚ) (w : Assignment) : ℚ := (36 * w 1) + (28 * w 1 * w 35) + (-57 * w 1 * w 36) + (48 * w 1 * w 74) + (-88 * w 1 * w 75) + (-39 * w 2) + (-57 * w 2 * w 35) + (56 * w 2 * w 36) + (-88 * w 2 * w 74) + (96 * w 2 * w 75) + (14 * w 3 * w 102) + (-8 * w 3 * w 103) + (-8 * w 4 * w 102) + (28 * w 4 * w 103)

@[expose] def r355 (S : ℚ) (w : Assignment) : ℚ := (6 * w 17) + (-1 * w 17 * w 19) + (-2 * w 18 * w 20) + (5 * w 94 * w 104) + (10 * w 95 * w 105)

@[expose] def r356 (S : ℚ) (w : Assignment) : ℚ := (1 * w 17 * w 20) + (-6 * w 18) + (1 * w 18 * w 19) + (-5 * w 94 * w 105) + (-5 * w 95 * w 104)

@[expose] def r357 (S : ℚ) (w : Assignment) : ℚ := (39 * w 5) + (57 * w 5 * w 35) + (-56 * w 5 * w 36) + (88 * w 5 * w 74) + (-96 * w 5 * w 75) + (-72 * w 6) + (-56 * w 6 * w 35) + (114 * w 6 * w 36) + (-96 * w 6 * w 74) + (176 * w 6 * w 75) + (8 * w 7 * w 106) + (-28 * w 7 * w 107) + (-28 * w 8 * w 106) + (16 * w 8 * w 107)

@[expose] def r358 (S : ℚ) (w : Assignment) : ℚ := (36 * w 5) + (28 * w 5 * w 35) + (-57 * w 5 * w 36) + (48 * w 5 * w 74) + (-88 * w 5 * w 75) + (-39 * w 6) + (-57 * w 6 * w 35) + (56 * w 6 * w 36) + (-88 * w 6 * w 74) + (96 * w 6 * w 75) + (14 * w 7 * w 106) + (-8 * w 7 * w 107) + (-8 * w 8 * w 106) + (28 * w 8 * w 107)

@[expose] def r359 (S : ℚ) (w : Assignment) : ℚ := (39 * w 9) + (57 * w 9 * w 35) + (-56 * w 9 * w 36) + (88 * w 9 * w 74) + (-96 * w 9 * w 75) + (-72 * w 10) + (-56 * w 10 * w 35) + (114 * w 10 * w 36) + (-96 * w 10 * w 74) + (176 * w 10 * w 75) + (8 * w 11 * w 110) + (-28 * w 11 * w 111) + (-28 * w 12 * w 110) + (16 * w 12 * w 111)

@[expose] def r360 (S : ℚ) (w : Assignment) : ℚ := (36 * w 9) + (28 * w 9 * w 35) + (-57 * w 9 * w 36) + (48 * w 9 * w 74) + (-88 * w 9 * w 75) + (-39 * w 10) + (-57 * w 10 * w 35) + (56 * w 10 * w 36) + (-88 * w 10 * w 74) + (96 * w 10 * w 75) + (14 * w 11 * w 110) + (-8 * w 11 * w 111) + (-8 * w 12 * w 110) + (28 * w 12 * w 111)

@[expose] def r361 (S : ℚ) (w : Assignment) : ℚ := (39 * w 13) + (57 * w 13 * w 35) + (-56 * w 13 * w 36) + (88 * w 13 * w 74) + (-96 * w 13 * w 75) + (-72 * w 14) + (-56 * w 14 * w 35) + (114 * w 14 * w 36) + (-96 * w 14 * w 74) + (176 * w 14 * w 75) + (8 * w 15 * w 114) + (-28 * w 15 * w 115) + (-28 * w 16 * w 114) + (16 * w 16 * w 115)

@[expose] def r362 (S : ℚ) (w : Assignment) : ℚ := (36 * w 13) + (28 * w 13 * w 35) + (-57 * w 13 * w 36) + (48 * w 13 * w 74) + (-88 * w 13 * w 75) + (-39 * w 14) + (-57 * w 14 * w 35) + (56 * w 14 * w 36) + (-88 * w 14 * w 74) + (96 * w 14 * w 75) + (14 * w 15 * w 114) + (-8 * w 15 * w 115) + (-8 * w 16 * w 114) + (28 * w 16 * w 115)

@[expose] def r363 (S : ℚ) (w : Assignment) : ℚ := (1 * w 0 * w 0) + (-1 * w 118)

@[expose] def r364 (S : ℚ) (w : Assignment) : ℚ := (1 * w 106 * w 114) + (2 * w 107 * w 115) + (-1 * w 119)

@[expose] def r365 (S : ℚ) (w : Assignment) : ℚ := (1 * w 106 * w 115) + (1 * w 107 * w 114) + (-1 * w 120)

@[expose] def r366 (S : ℚ) (w : Assignment) : ℚ := (1 * w 106 * w 110) + (2 * w 107 * w 111) + (-1 * w 121)

@[expose] def r367 (S : ℚ) (w : Assignment) : ℚ := (1 * w 106 * w 111) + (1 * w 107 * w 110) + (-1 * w 122)

@[expose] def r368 (S : ℚ) (w : Assignment) : ℚ := (1 * w 110 * w 110) + (2 * w 111 * w 111) + (4 * w 114 * w 114) + (-4 * w 114 * w 119) + (2 * w 114 * w 121) + (8 * w 115 * w 115) + (-8 * w 115 * w 120) + (4 * w 115 * w 122) + (1 * w 119 * w 119) + (-1 * w 119 * w 121) + (2 * w 120 * w 120) + (-2 * w 120 * w 122) + (-1 * w 123)

@[expose] def r369 (S : ℚ) (w : Assignment) : ℚ := (2 * w 110 * w 111) + (8 * w 114 * w 115) + (-4 * w 114 * w 120) + (2 * w 114 * w 122) + (-4 * w 115 * w 119) + (2 * w 115 * w 121) + (2 * w 119 * w 120) + (-1 * w 119 * w 122) + (-1 * w 120 * w 121) + (-2 * w 124)

@[expose] def r370 (S : ℚ) (w : Assignment) : ℚ := (1 * w 90 * w 90) + (-8 * w 91 * w 91) + (-1 * w 125)

@[expose] def r371 (S : ℚ) (w : Assignment) : ℚ := (1 * w 37 * w 37) + (-1 * w 126)

@[expose] def r372 (S : ℚ) (w : Assignment) : ℚ := (1 * w 102 * w 102) + (-2 * w 102 * w 104) + (2 * w 103 * w 103) + (4 * w 103 * w 105) + (1 * w 104 * w 104) + (2 * w 105 * w 105) + (-1 * w 127)

@[expose] def r373 (S : ℚ) (w : Assignment) : ℚ := (1 * w 102 * w 103) + (1 * w 102 * w 105) + (-1 * w 103 * w 104) + (-1 * w 104 * w 105) + (-1 * w 128)

@[expose] def r374 (S : ℚ) (w : Assignment) : ℚ := (1 * w 106 * w 106) + (-2 * w 106 * w 108) + (2 * w 107 * w 107) + (4 * w 107 * w 109) + (1 * w 108 * w 108) + (2 * w 109 * w 109) + (-1 * w 129)

@[expose] def r375 (S : ℚ) (w : Assignment) : ℚ := (1 * w 106 * w 107) + (1 * w 106 * w 109) + (-1 * w 107 * w 108) + (-1 * w 108 * w 109) + (-1 * w 130)

@[expose] def r376 (S : ℚ) (w : Assignment) : ℚ := (1 * w 110 * w 110) + (-2 * w 110 * w 112) + (2 * w 111 * w 111) + (4 * w 111 * w 113) + (1 * w 112 * w 112) + (2 * w 113 * w 113) + (-1 * w 131)

@[expose] def r377 (S : ℚ) (w : Assignment) : ℚ := (1 * w 110 * w 111) + (1 * w 110 * w 113) + (-1 * w 111 * w 112) + (-1 * w 112 * w 113) + (-1 * w 132)

@[expose] def r378 (S : ℚ) (w : Assignment) : ℚ := (1 * w 114 * w 114) + (-2 * w 114 * w 116) + (2 * w 115 * w 115) + (4 * w 115 * w 117) + (1 * w 116 * w 116) + (2 * w 117 * w 117) + (-1 * w 133)

@[expose] def r379 (S : ℚ) (w : Assignment) : ℚ := (1 * w 114 * w 115) + (1 * w 114 * w 117) + (-1 * w 115 * w 116) + (-1 * w 116 * w 117) + (-1 * w 134)

@[expose] def r380 (S : ℚ) (w : Assignment) : ℚ := (221771664 * w 0 * w 0) + (-29784 * w 0 * w 102) + (443543328 * w 0 * w 118) + (1 * w 102 * w 102) + (-29784 * w 102 * w 118) + (2 * w 103 * w 103) + (221771664 * w 118 * w 118) + (-221771664 * w 135)

@[expose] def r381 (S : ℚ) (w : Assignment) : ℚ := (14892 * w 0 * w 103) + (-1 * w 102 * w 103) + (14892 * w 103 * w 118) + (-14892 * w 136)

@[expose] def r382 (S : ℚ) (w : Assignment) : ℚ := (1 * w 123 * w 123) + (8 * w 124 * w 124) + (-1 * w 137)

@[expose] def r383 (S : ℚ) (w : Assignment) : ℚ := (1 * w 123 * w 124) + (-1 * w 138)

@[expose] def r384 (S : ℚ) (w : Assignment) : ℚ := (1 * w 79 * w 82) + (2 * w 80 * w 83) + (-1 * w 139)

@[expose] def r385 (S : ℚ) (w : Assignment) : ℚ := (1 * w 79 * w 83) + (1 * w 80 * w 82) + (-1 * w 140)

@[expose] def r386 (S : ℚ) (w : Assignment) : ℚ := (1 * w 85 * w 139) + (2 * w 86 * w 140) + (-1 * w 141)

@[expose] def r387 (S : ℚ) (w : Assignment) : ℚ := (1 * w 85 * w 140) + (1 * w 86 * w 139) + (-1 * w 142)

@[expose] def r388 (S : ℚ) (w : Assignment) : ℚ := (1 * w 88 * w 141) + (2 * w 89 * w 142) + (-1 * w 143)

@[expose] def r389 (S : ℚ) (w : Assignment) : ℚ := (1 * w 88 * w 142) + (1 * w 89 * w 141) + (-1 * w 144)

@[expose] def r390 (S : ℚ) (w : Assignment) : ℚ := (1 * w 143 * w 143) + (-2 * w 144 * w 144) + (-1 * w 145)

@[expose] def r391 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 38 * w 146)

@[expose] def r392 (S : ℚ) (w : Assignment) : ℚ := (1 * w 38 * w 38) + (-1 * w 147)

@[expose] def r393 (S : ℚ) (w : Assignment) : ℚ := (1 * w 38 * w 147) + (-1 * w 148)

@[expose] def r394 (S : ℚ) (w : Assignment) : ℚ := (1205412 * w 38 * w 147) + (3081901 * w 147 * w 147) + (1952786 * w 147 * w 148) + (-3081901 * w 149)

@[expose] def r395 (S : ℚ) (w : Assignment) : ℚ := (1952786) + (-3905572 * w 38) + (32 * w 38 * w 151) + (1952786 * w 147) + (-76265 * w 147 * w 151) + (-3081901 * w 149 * w 151)

@[expose] def r396 (S : ℚ) (w : Assignment) : ℚ := (1 * w 38 * w 151) + (1 * w 38 * w 152) + (-1 * w 153)

@[expose] def r397 (S : ℚ) (w : Assignment) : ℚ := (1 * w 151 * w 151) + (2 * w 151 * w 152) + (1 * w 152 * w 152) + (-1 * w 154)

@[expose] def r398 (S : ℚ) (w : Assignment) : ℚ := (1) + (1 * w 126 * w 156) + (-1 * w 159)

@[expose] def r399 (S : ℚ) (w : Assignment) : ℚ := (1 * w 125 * w 151) + (1 * w 159 * w 159) + (-1 * w 160)

@[expose] def r400 (S : ℚ) (w : Assignment) : ℚ := (1 * w 58 * w 151) + (1 * w 160 * w 160) + (-1 * w 161)

@[expose] def r401 (S : ℚ) (w : Assignment) : ℚ := (2 * w 59 * w 151) + (-1 * w 162)

@[expose] def r402 (S : ℚ) (w : Assignment) : ℚ := (1 * w 60 * w 151) + (1 * w 161 * w 161) + (2 * w 162 * w 162) + (-1 * w 163)

@[expose] def r403 (S : ℚ) (w : Assignment) : ℚ := (2 * w 61 * w 151) + (2 * w 161 * w 162) + (-1 * w 164)

@[expose] def r404 (S : ℚ) (w : Assignment) : ℚ := (2 * w 62 * w 151) + (1 * w 163 * w 163) + (2 * w 164 * w 164) + (-1 * w 165)

@[expose] def r405 (S : ℚ) (w : Assignment) : ℚ := (2 * w 63 * w 151) + (2 * w 163 * w 164) + (-1 * w 166)

@[expose] def r406 (S : ℚ) (w : Assignment) : ℚ := (1 * w 64 * w 151) + (1 * w 165 * w 165) + (2 * w 166 * w 166) + (-1 * w 167)

@[expose] def r407 (S : ℚ) (w : Assignment) : ℚ := (2 * w 65 * w 151) + (2 * w 165 * w 166) + (-1 * w 168)

@[expose] def r408 (S : ℚ) (w : Assignment) : ℚ := (1 * w 19 * w 151) + (-1 * w 151) + (1 * w 167 * w 167) + (2 * w 168 * w 168) + (-1 * w 169)

@[expose] def r409 (S : ℚ) (w : Assignment) : ℚ := (1 * w 23 * w 151) + (-1 * w 151) + (1 * w 169 * w 169) + (2 * w 170 * w 170) + (-1 * w 171)

@[expose] def r410 (S : ℚ) (w : Assignment) : ℚ := (1 * w 27 * w 151) + (-1 * w 151) + (1 * w 171 * w 171) + (2 * w 172 * w 172) + (-1 * w 173)

@[expose] def r411 (S : ℚ) (w : Assignment) : ℚ := (1 * w 31 * w 151) + (-1 * w 151) + (1 * w 173 * w 173) + (2 * w 174 * w 174) + (-1 * w 175)

@[expose] def r412 (S : ℚ) (w : Assignment) : ℚ := (1 * w 127 * w 156) + (1 * w 175 * w 175) + (2 * w 176 * w 176) + (-1 * w 177)

@[expose] def r413 (S : ℚ) (w : Assignment) : ℚ := (2 * w 128 * w 156) + (2 * w 175 * w 176) + (-1 * w 178)

@[expose] def r414 (S : ℚ) (w : Assignment) : ℚ := (1 * w 129 * w 158) + (1 * w 177 * w 177) + (2 * w 178 * w 178) + (-1 * w 179)

@[expose] def r415 (S : ℚ) (w : Assignment) : ℚ := (2 * w 130 * w 158) + (2 * w 177 * w 178) + (-1 * w 180)

@[expose] def r416 (S : ℚ) (w : Assignment) : ℚ := (1 * w 131 * w 158) + (1 * w 179 * w 179) + (2 * w 180 * w 180) + (-1 * w 181)

@[expose] def r417 (S : ℚ) (w : Assignment) : ℚ := (2 * w 132 * w 158) + (2 * w 179 * w 180) + (-1 * w 182)

@[expose] def r418 (S : ℚ) (w : Assignment) : ℚ := (1 * w 133 * w 158) + (1 * w 181 * w 181) + (2 * w 182 * w 182) + (-1 * w 183)

@[expose] def r419 (S : ℚ) (w : Assignment) : ℚ := (2 * w 134 * w 158) + (2 * w 181 * w 182) + (-1 * w 184)

@[expose] def r420 (S : ℚ) (w : Assignment) : ℚ := (110885832 * w 0 * w 156) + (-7446 * w 102 * w 156) + (110885832 * w 118 * w 156) + (221771664 * w 135 * w 156) + (13860729 * w 156) + (1 * w 183 * w 183) + (2 * w 184 * w 184) + (-1 * w 185)

@[expose] def r421 (S : ℚ) (w : Assignment) : ℚ := (1 * w 187 * w 187) + (-2 * w 187 * w 189) + (-2 * w 188 * w 188)

@[expose] def r422 (S : ℚ) (w : Assignment) : ℚ := (1 * w 39 * w 190) + (-1 * w 191)

@[expose] def r423 (S : ℚ) (w : Assignment) : ℚ := (1 * w 40 * w 40) + (-1 * w 192)

@[expose] def r424 (S : ℚ) (w : Assignment) : ℚ := (867 * w 39 * w 39) + (-102 * w 39 * w 191) + (-34 * w 39 * w 192) + (3 * w 191 * w 191) + (2 * w 191 * w 192) + (-1 * w 192 * w 192) + (-3 * w 193)

@[expose] def r425 (S : ℚ) (w : Assignment) : ℚ := (1 * w 143 * w 143) + (2 * w 143 * w 145) + (1 * w 145 * w 145) + (-1 * w 146 * w 194)

@[expose] def r426 (S : ℚ) (w : Assignment) : ℚ := (1 * w 194 * w 194) + (-1 * w 195)

@[expose] def r427 (S : ℚ) (w : Assignment) : ℚ := (1 * w 194 * w 195) + (-1 * w 196)

@[expose] def r428 (S : ℚ) (w : Assignment) : ℚ := (1205412 * w 194 * w 195) + (3081901 * w 195 * w 195) + (1952786 * w 195 * w 196) + (-1205412 * w 197)

@[expose] def r429 (S : ℚ) (w : Assignment) : ℚ := (1 * w 146 * w 194) + (-1 * w 146 * w 195) + (-1 * w 198)

@[expose] def r430 (S : ℚ) (w : Assignment) : ℚ := (1 * w 198 * w 198) + (-1 * w 199)

@[expose] def r431 (S : ℚ) (w : Assignment) : ℚ := (1 * w 199 * w 199) + (-1 * w 200)

@[expose] def r432 (S : ℚ) (w : Assignment) : ℚ := (32 * w 194 * w 201) + (-76265 * w 195 * w 201) + (-1205412 * w 197 * w 201) + (-1952786 * w 198 * w 200)

@[expose] def r433 (S : ℚ) (w : Assignment) : ℚ := (2 * w 194 * w 194) + (-1 * w 194 * w 195) + (-2 * w 202)

@[expose] def r434 (S : ℚ) (w : Assignment) : ℚ := (1 * w 194 * w 201) + (-1 * w 204)

@[expose] def r435 (S : ℚ) (w : Assignment) : ℚ := (1 * w 201 * w 201) + (-1 * w 205)

@[expose] def r436 (S : ℚ) (w : Assignment) : ℚ := (1 * w 201 * w 207) + (-1 * w 204 * w 207) + (1 * w 206 * w 206)

@[expose] def r437 (S : ℚ) (w : Assignment) : ℚ := (1) + (1 * w 126 * w 207) + (-1 * w 210)

@[expose] def r438 (S : ℚ) (w : Assignment) : ℚ := (1 * w 125 * w 203) + (1 * w 210 * w 210) + (-1 * w 211)

@[expose] def r439 (S : ℚ) (w : Assignment) : ℚ := (1 * w 58 * w 203) + (1 * w 211 * w 211) + (-1 * w 212)

@[expose] def r440 (S : ℚ) (w : Assignment) : ℚ := (2 * w 59 * w 203) + (-1 * w 213)

@[expose] def r441 (S : ℚ) (w : Assignment) : ℚ := (1 * w 60 * w 203) + (1 * w 212 * w 212) + (2 * w 213 * w 213) + (-1 * w 214)

@[expose] def r442 (S : ℚ) (w : Assignment) : ℚ := (2 * w 61 * w 203) + (2 * w 212 * w 213) + (-1 * w 215)

@[expose] def r443 (S : ℚ) (w : Assignment) : ℚ := (2 * w 62 * w 203) + (1 * w 214 * w 214) + (2 * w 215 * w 215) + (-1 * w 216)

@[expose] def r444 (S : ℚ) (w : Assignment) : ℚ := (2 * w 63 * w 203) + (2 * w 214 * w 215) + (-1 * w 217)

@[expose] def r445 (S : ℚ) (w : Assignment) : ℚ := (1 * w 64 * w 203) + (1 * w 216 * w 216) + (2 * w 217 * w 217) + (-1 * w 218)

@[expose] def r446 (S : ℚ) (w : Assignment) : ℚ := (2 * w 65 * w 203) + (2 * w 216 * w 217) + (-1 * w 219)

@[expose] def r447 (S : ℚ) (w : Assignment) : ℚ := (1 * w 19 * w 203) + (-1 * w 203) + (1 * w 218 * w 218) + (2 * w 219 * w 219) + (-1 * w 220)

@[expose] def r448 (S : ℚ) (w : Assignment) : ℚ := (1 * w 23 * w 203) + (-1 * w 203) + (1 * w 220 * w 220) + (2 * w 221 * w 221) + (-1 * w 222)

@[expose] def r449 (S : ℚ) (w : Assignment) : ℚ := (1 * w 27 * w 203) + (-1 * w 203) + (1 * w 222 * w 222) + (2 * w 223 * w 223) + (-1 * w 224)

@[expose] def r450 (S : ℚ) (w : Assignment) : ℚ := (1 * w 31 * w 203) + (-1 * w 203) + (1 * w 224 * w 224) + (2 * w 225 * w 225) + (-1 * w 226)

@[expose] def r451 (S : ℚ) (w : Assignment) : ℚ := (1 * w 127 * w 207) + (1 * w 226 * w 226) + (2 * w 227 * w 227) + (-1 * w 228)

@[expose] def r452 (S : ℚ) (w : Assignment) : ℚ := (2 * w 128 * w 207) + (2 * w 226 * w 227) + (-1 * w 229)

@[expose] def r453 (S : ℚ) (w : Assignment) : ℚ := (1 * w 129 * w 209) + (1 * w 228 * w 228) + (2 * w 229 * w 229) + (-1 * w 230)

@[expose] def r454 (S : ℚ) (w : Assignment) : ℚ := (2 * w 130 * w 209) + (2 * w 228 * w 229) + (-1 * w 231)

@[expose] def r455 (S : ℚ) (w : Assignment) : ℚ := (1 * w 131 * w 209) + (1 * w 230 * w 230) + (2 * w 231 * w 231) + (-1 * w 232)

@[expose] def r456 (S : ℚ) (w : Assignment) : ℚ := (2 * w 132 * w 209) + (2 * w 230 * w 231) + (-1 * w 233)

@[expose] def r457 (S : ℚ) (w : Assignment) : ℚ := (1 * w 133 * w 209) + (1 * w 232 * w 232) + (2 * w 233 * w 233) + (-1 * w 234)

@[expose] def r458 (S : ℚ) (w : Assignment) : ℚ := (2 * w 134 * w 209) + (2 * w 232 * w 233) + (-1 * w 235)

@[expose] def r459 (S : ℚ) (w : Assignment) : ℚ := (110885832 * w 0 * w 207) + (-7446 * w 102 * w 207) + (110885832 * w 118 * w 207) + (221771664 * w 135 * w 207) + (13860729 * w 207) + (1 * w 234 * w 234) + (2 * w 235 * w 235) + (-1 * w 236)

@[expose] def r460 (S : ℚ) (w : Assignment) : ℚ := (1 * w 238 * w 238) + (-2 * w 238 * w 240) + (-2 * w 239 * w 239)

@[expose] def r461 (S : ℚ) (w : Assignment) : ℚ := (1 * w 201 * w 241) + (-1 * w 204 * w 241) + (1 * w 240 * w 240)

@[expose] def r462 (S : ℚ) (w : Assignment) : ℚ := (1 * w 43 * w 241) + (-1 * w 242)

@[expose] def r463 (S : ℚ) (w : Assignment) : ℚ := (1 * w 44 * w 44) + (-1 * w 243)

@[expose] def r464 (S : ℚ) (w : Assignment) : ℚ := (867 * w 43 * w 43) + (-102 * w 43 * w 242) + (-34 * w 43 * w 243) + (3 * w 242 * w 242) + (2 * w 242 * w 243) + (-1 * w 243 * w 243) + (-3 * w 244)

@[expose] def r465 (S : ℚ) (w : Assignment) : ℚ := (1 * w 145 * w 145) + (-1 * w 146 * w 245)

@[expose] def r466 (S : ℚ) (w : Assignment) : ℚ := (1 * w 245 * w 245) + (-1 * w 246)

@[expose] def r467 (S : ℚ) (w : Assignment) : ℚ := (1 * w 245 * w 246) + (-1 * w 247)

@[expose] def r468 (S : ℚ) (w : Assignment) : ℚ := (1205412 * w 245 * w 246) + (3081901 * w 246 * w 246) + (1952786 * w 246 * w 247) + (-1205412 * w 248)

@[expose] def r469 (S : ℚ) (w : Assignment) : ℚ := (1 * w 146 * w 245) + (-1 * w 146 * w 246) + (-1 * w 249)

@[expose] def r470 (S : ℚ) (w : Assignment) : ℚ := (1 * w 249 * w 249) + (-1 * w 250)

@[expose] def r471 (S : ℚ) (w : Assignment) : ℚ := (1 * w 250 * w 250) + (-1 * w 251)

@[expose] def r472 (S : ℚ) (w : Assignment) : ℚ := (32 * w 245 * w 252) + (-76265 * w 246 * w 252) + (-1205412 * w 248 * w 252) + (-1952786 * w 249 * w 251)

@[expose] def r473 (S : ℚ) (w : Assignment) : ℚ := (2 * w 245 * w 245) + (-1 * w 245 * w 246) + (-2 * w 253)

@[expose] def r474 (S : ℚ) (w : Assignment) : ℚ := (1 * w 245 * w 252) + (-1 * w 255)

@[expose] def r475 (S : ℚ) (w : Assignment) : ℚ := (1 * w 252 * w 252) + (-1 * w 256)

@[expose] def r476 (S : ℚ) (w : Assignment) : ℚ := (1 * w 252 * w 258) + (-1 * w 255 * w 258) + (1 * w 257 * w 257)

@[expose] def r477 (S : ℚ) (w : Assignment) : ℚ := (1) + (1 * w 126 * w 258) + (-1 * w 261)

@[expose] def r478 (S : ℚ) (w : Assignment) : ℚ := (1 * w 125 * w 254) + (1 * w 261 * w 261) + (-1 * w 262)

@[expose] def r479 (S : ℚ) (w : Assignment) : ℚ := (1 * w 58 * w 254) + (1 * w 262 * w 262) + (-1 * w 263)

@[expose] def r480 (S : ℚ) (w : Assignment) : ℚ := (2 * w 59 * w 254) + (-1 * w 264)

@[expose] def r481 (S : ℚ) (w : Assignment) : ℚ := (1 * w 60 * w 254) + (1 * w 263 * w 263) + (2 * w 264 * w 264) + (-1 * w 265)

@[expose] def r482 (S : ℚ) (w : Assignment) : ℚ := (2 * w 61 * w 254) + (2 * w 263 * w 264) + (-1 * w 266)

@[expose] def r483 (S : ℚ) (w : Assignment) : ℚ := (2 * w 62 * w 254) + (1 * w 265 * w 265) + (2 * w 266 * w 266) + (-1 * w 267)

@[expose] def r484 (S : ℚ) (w : Assignment) : ℚ := (2 * w 63 * w 254) + (2 * w 265 * w 266) + (-1 * w 268)

@[expose] def r485 (S : ℚ) (w : Assignment) : ℚ := (1 * w 64 * w 254) + (1 * w 267 * w 267) + (2 * w 268 * w 268) + (-1 * w 269)

@[expose] def r486 (S : ℚ) (w : Assignment) : ℚ := (2 * w 65 * w 254) + (2 * w 267 * w 268) + (-1 * w 270)

@[expose] def r487 (S : ℚ) (w : Assignment) : ℚ := (1 * w 19 * w 254) + (-1 * w 254) + (1 * w 269 * w 269) + (2 * w 270 * w 270) + (-1 * w 271)

@[expose] def r488 (S : ℚ) (w : Assignment) : ℚ := (1 * w 23 * w 254) + (-1 * w 254) + (1 * w 271 * w 271) + (2 * w 272 * w 272) + (-1 * w 273)

@[expose] def r489 (S : ℚ) (w : Assignment) : ℚ := (1 * w 27 * w 254) + (-1 * w 254) + (1 * w 273 * w 273) + (2 * w 274 * w 274) + (-1 * w 275)

@[expose] def r490 (S : ℚ) (w : Assignment) : ℚ := (1 * w 31 * w 254) + (-1 * w 254) + (1 * w 275 * w 275) + (2 * w 276 * w 276) + (-1 * w 277)

@[expose] def r491 (S : ℚ) (w : Assignment) : ℚ := (1 * w 127 * w 258) + (1 * w 277 * w 277) + (2 * w 278 * w 278) + (-1 * w 279)

@[expose] def r492 (S : ℚ) (w : Assignment) : ℚ := (2 * w 128 * w 258) + (2 * w 277 * w 278) + (-1 * w 280)

@[expose] def r493 (S : ℚ) (w : Assignment) : ℚ := (1 * w 129 * w 260) + (1 * w 279 * w 279) + (2 * w 280 * w 280) + (-1 * w 281)

@[expose] def r494 (S : ℚ) (w : Assignment) : ℚ := (2 * w 130 * w 260) + (2 * w 279 * w 280) + (-1 * w 282)

@[expose] def r495 (S : ℚ) (w : Assignment) : ℚ := (1 * w 131 * w 260) + (1 * w 281 * w 281) + (2 * w 282 * w 282) + (-1 * w 283)

@[expose] def r496 (S : ℚ) (w : Assignment) : ℚ := (2 * w 132 * w 260) + (2 * w 281 * w 282) + (-1 * w 284)

@[expose] def r497 (S : ℚ) (w : Assignment) : ℚ := (1 * w 133 * w 260) + (1 * w 283 * w 283) + (2 * w 284 * w 284) + (-1 * w 285)

@[expose] def r498 (S : ℚ) (w : Assignment) : ℚ := (2 * w 134 * w 260) + (2 * w 283 * w 284) + (-1 * w 286)

@[expose] def r499 (S : ℚ) (w : Assignment) : ℚ := (110885832 * w 0 * w 258) + (-7446 * w 102 * w 258) + (110885832 * w 118 * w 258) + (221771664 * w 135 * w 258) + (13860729 * w 258) + (1 * w 285 * w 285) + (2 * w 286 * w 286) + (-1 * w 287)

@[expose] def r500 (S : ℚ) (w : Assignment) : ℚ := (1 * w 289 * w 289) + (-2 * w 289 * w 291) + (-2 * w 290 * w 290)

@[expose] def r501 (S : ℚ) (w : Assignment) : ℚ := (1 * w 252 * w 292) + (-1 * w 255 * w 292) + (1 * w 291 * w 291)

@[expose] def r502 (S : ℚ) (w : Assignment) : ℚ := (1 * w 47 * w 292) + (-1 * w 293)

@[expose] def r503 (S : ℚ) (w : Assignment) : ℚ := (1 * w 48 * w 48) + (-1 * w 294)

@[expose] def r504 (S : ℚ) (w : Assignment) : ℚ := (867 * w 47 * w 47) + (-102 * w 47 * w 293) + (-34 * w 47 * w 294) + (3 * w 293 * w 293) + (2 * w 293 * w 294) + (-1 * w 294 * w 294) + (-3 * w 295)

@[expose] def r505 (S : ℚ) (w : Assignment) : ℚ := (1 * w 0 * w 0) + (2 * w 0 * w 118) + (1 * w 118 * w 118) + (-1 * w 296)

@[expose] def r506 (S : ℚ) (w : Assignment) : ℚ := (100291113 * w 0 * w 0) + (200582226 * w 0 * w 118) + (496408687 * w 0 * w 296) + (100291113 * w 118 * w 118) + (496408687 * w 118 * w 296) + (591391104 * w 296 * w 296) + (-100291113 * w 297)

@[expose] def r507 (S : ℚ) (w : Assignment) : ℚ := (1) + (-101783690143177584 * w 0 * w 298) + (-101783690143177584 * w 118 * w 298) + (-267108917866935984 * w 296 * w 298) + (-533801448346128768 * w 297 * w 298) + (-4376874610839020 * w 298)

@[expose] def r508 (S : ℚ) (w : Assignment) : ℚ := (1 * w 298 * w 298) + (-1 * w 299)

@[expose] def r509 (S : ℚ) (w : Assignment) : ℚ := (1 * w 299 * w 299) + (-1 * w 300)

@[expose] def r510 (S : ℚ) (w : Assignment) : ℚ := (1 * w 300 * w 300) + (-1 * w 301)

@[expose] def r511 (S : ℚ) (w : Assignment) : ℚ := (1 * w 301 * w 301) + (-1 * w 302)

@[expose] def r512 (S : ℚ) (w : Assignment) : ℚ := (1 * w 82 * w 303) + (2 * w 83 * w 304) + (-1 * w 305)

@[expose] def r513 (S : ℚ) (w : Assignment) : ℚ := (1 * w 82 * w 304) + (1 * w 83 * w 303) + (-1 * w 306)

@[expose] def r514 (S : ℚ) (w : Assignment) : ℚ := (88) + (57 * w 82 * w 82) + (-112 * w 82 * w 83) + (114 * w 83 * w 83) + (57 * w 303 * w 303) + (-112 * w 303 * w 304) + (114 * w 304 * w 304) + (78 * w 305) + (-8 * w 305 * w 305) + (-144 * w 306) + (-16 * w 306 * w 306)

@[expose] def r515 (S : ℚ) (w : Assignment) : ℚ := (24) + (14 * w 82 * w 82) + (-57 * w 82 * w 83) + (28 * w 83 * w 83) + (14 * w 303 * w 303) + (-57 * w 303 * w 304) + (28 * w 304 * w 304) + (36 * w 305) + (8 * w 305 * w 306) + (-39 * w 306)

@[expose] def r516 (S : ℚ) (w : Assignment) : ℚ := (1 * w 303 * w 303) + (-2 * w 304 * w 304) + (-1 * w 307)

@[expose] def r517 (S : ℚ) (w : Assignment) : ℚ := (1) + (-1 * w 307 * w 308)

@[expose] def r518 (S : ℚ) (w : Assignment) : ℚ := (1 * w 302 * w 308) + (-1 * w 309 * w 310)

@[expose] def r519 (S : ℚ) (w : Assignment) : ℚ := (2 * w 33 * w 298) + (1 * w 309 * w 309) + (-1 * w 311)

@[expose] def r520 (S : ℚ) (w : Assignment) : ℚ := (1 * w 310 * w 310) + (-1 * w 312)

@[expose] def r521 (S : ℚ) (w : Assignment) : ℚ := (1) + (101783690143177584 * w 0 * w 312) + (-11648532634745815423296 * w 0 * w 313) + (101783690143177584 * w 118 * w 312) + (-11648532634745815423296 * w 118 * w 313) + (267108917866935984 * w 296 * w 312) + (-30569012996363621752896 * w 296 * w 313) + (533801448346128768 * w 297 * w 312) + (-61090372954524360724992 * w 297 * w 313) + (2 * w 311) + (1 * w 311 * w 311) + (4376874610839020 * w 312) + (-500907037962860804881 * w 313)

@[expose] def r522 (S : ℚ) (w : Assignment) : ℚ := (1 * w 51 * w 314) + (-1 * w 315)

@[expose] def r523 (S : ℚ) (w : Assignment) : ℚ := (1 * w 52 * w 52) + (-1 * w 316)

@[expose] def r524 (S : ℚ) (w : Assignment) : ℚ := (867 * w 51 * w 51) + (-102 * w 51 * w 315) + (-34 * w 51 * w 316) + (3 * w 315 * w 315) + (2 * w 315 * w 316) + (-1 * w 316 * w 316) + (-3 * w 317)

@[expose] def stage3 (S : ℚ) : List Row := [r290 S, r291 S, r292 S, r293 S, r294 S, r295 S, r296 S, r297 S, r298 S, r299 S, r300 S, r301 S, r302 S, r303 S, r304 S, r305 S, r306 S, r307 S, r308 S, r309 S, r310 S, r311 S, r312 S, r313 S, r314 S, r315 S, r316 S, r317 S, r318 S, r319 S, r320 S, r321 S, r322 S, r323 S, r324 S, r325 S, r326 S, r327 S, r328 S, r329 S, r330 S, r331 S, r332 S, r333 S, r334 S, r335 S, r336 S, r337 S, r338 S, r339 S, r340 S, r341 S, r342 S, r343 S, r344 S, r345 S, r346 S, r347 S, r348 S, r349 S, r350 S, r351 S, r352 S, r353 S, r354 S, r355 S, r356 S, r357 S, r358 S, r69 S, r70 S, r359 S, r360 S, r73 S, r74 S, r361 S, r362 S, r77 S, r78 S, r363 S, r364 S, r365 S, r366 S, r367 S, r368 S, r369 S, r370 S, r371 S, r372 S, r373 S, r374 S, r375 S, r376 S, r377 S, r378 S, r379 S, r380 S, r381 S, r382 S, r383 S, r384 S, r385 S, r386 S, r387 S, r388 S, r389 S, r390 S, r391 S, r392 S, r393 S, r394 S, r111 S, r395 S, r113 S, r396 S, r397 S, r116 S, r117 S, r118 S, r119 S, r398 S, r399 S, r400 S, r401 S, r402 S, r403 S, r404 S, r405 S, r406 S, r407 S, r408 S, r131 S, r409 S, r133 S, r410 S, r135 S, r411 S, r137 S, r412 S, r413 S, r414 S, r415 S, r416 S, r417 S, r418 S, r419 S, r420 S, r147 S, r148 S, r149 S, r421 S, r151 S, r422 S, r423 S, r154 S, r424 S, r156 S, r425 S, r426 S, r427 S, r428 S, r429 S, r430 S, r431 S, r432 S, r433 S, r166 S, r434 S, r435 S, r169 S, r436 S, r171 S, r172 S, r437 S, r438 S, r439 S, r440 S, r441 S, r442 S, r443 S, r444 S, r445 S, r446 S, r447 S, r184 S, r448 S, r186 S, r449 S, r188 S, r450 S, r190 S, r451 S, r452 S, r453 S, r454 S, r455 S, r456 S, r457 S, r458 S, r459 S, r200 S, r201 S, r202 S, r460 S, r461 S, r462 S, r463 S, r207 S, r464 S, r209 S, r465 S, r466 S, r467 S, r468 S, r469 S, r470 S, r471 S, r472 S, r473 S, r219 S, r474 S, r475 S, r222 S, r476 S, r224 S, r225 S, r477 S, r478 S, r479 S, r480 S, r481 S, r482 S, r483 S, r484 S, r485 S, r486 S, r487 S, r237 S, r488 S, r239 S, r489 S, r241 S, r490 S, r243 S, r491 S, r492 S, r493 S, r494 S, r495 S, r496 S, r497 S, r498 S, r499 S, r253 S, r254 S, r255 S, r500 S, r501 S, r502 S, r503 S, r260 S, r504 S, r262 S, r505 S, r506 S, r507 S, r508 S, r509 S, r510 S, r511 S, r512 S, r513 S, r514 S, r515 S, r516 S, r517 S, r276 S, r518 S, r519 S, r520 S, r521 S, r281 S, r522 S, r523 S, r524 S, r285 S, r286 S, r289 S]

@[expose] def r525 (S : ℚ) (w : Assignment) : ℚ := (1 * w 143 * w 143) + (-2 * w 144 * w 144) + ((-1 / 4096) * w 145)

@[expose] def r526 (S : ℚ) (w : Assignment) : ℚ := (1 * w 143 * w 143) + ((1 / 2048) * w 143 * w 145) + ((1 / 16777216) * w 145 * w 145) + (-1 * w 146 * w 194)

@[expose] def r527 (S : ℚ) (w : Assignment) : ℚ := ((1 / 16777216) * w 145 * w 145) + (-1 * w 146 * w 245)

@[expose] def r528 (S : ℚ) (w : Assignment) : ℚ := (1) + (1 * w 145 * w 307 * S^1) + (-1 * w 307 * w 308)

@[expose] def r529 (S : ℚ) (w : Assignment) : ℚ := (-1 * w 145 * w 302 * S^1) + (1 * w 302 * w 308) + (-1 * w 309 * w 310)

@[expose] def r530 (S : ℚ) (w : Assignment) : ℚ := (8 * w 55 * S^1) + (1 * w 55 * w 55) + (-6 * w 55 * w 56) + (6 * w 55 * w 57) + (15 * w 56 * w 56) + (-18 * w 56 * w 57) + (7 * w 57 * w 57) + (-48 * w 308 * w 308)

@[expose] def stage4 (S : ℚ) : List Row := [r290 S, r291 S, r292 S, r293 S, r294 S, r295 S, r296 S, r297 S, r298 S, r299 S, r300 S, r301 S, r302 S, r303 S, r304 S, r305 S, r306 S, r307 S, r308 S, r309 S, r310 S, r311 S, r312 S, r313 S, r314 S, r315 S, r316 S, r317 S, r318 S, r319 S, r320 S, r321 S, r322 S, r323 S, r324 S, r325 S, r326 S, r327 S, r328 S, r329 S, r330 S, r331 S, r332 S, r333 S, r334 S, r335 S, r336 S, r337 S, r338 S, r339 S, r340 S, r341 S, r342 S, r343 S, r344 S, r345 S, r346 S, r347 S, r348 S, r349 S, r350 S, r351 S, r352 S, r353 S, r354 S, r355 S, r356 S, r357 S, r358 S, r69 S, r70 S, r359 S, r360 S, r73 S, r74 S, r361 S, r362 S, r77 S, r78 S, r363 S, r364 S, r365 S, r366 S, r367 S, r368 S, r369 S, r370 S, r371 S, r372 S, r373 S, r374 S, r375 S, r376 S, r377 S, r378 S, r379 S, r380 S, r381 S, r382 S, r383 S, r384 S, r385 S, r386 S, r387 S, r388 S, r389 S, r525 S, r391 S, r392 S, r393 S, r394 S, r111 S, r395 S, r113 S, r396 S, r397 S, r116 S, r117 S, r118 S, r119 S, r398 S, r399 S, r400 S, r401 S, r402 S, r403 S, r404 S, r405 S, r406 S, r407 S, r408 S, r131 S, r409 S, r133 S, r410 S, r135 S, r411 S, r137 S, r412 S, r413 S, r414 S, r415 S, r416 S, r417 S, r418 S, r419 S, r420 S, r147 S, r148 S, r149 S, r421 S, r151 S, r422 S, r423 S, r154 S, r424 S, r156 S, r526 S, r426 S, r427 S, r428 S, r429 S, r430 S, r431 S, r432 S, r433 S, r166 S, r434 S, r435 S, r169 S, r436 S, r171 S, r172 S, r437 S, r438 S, r439 S, r440 S, r441 S, r442 S, r443 S, r444 S, r445 S, r446 S, r447 S, r184 S, r448 S, r186 S, r449 S, r188 S, r450 S, r190 S, r451 S, r452 S, r453 S, r454 S, r455 S, r456 S, r457 S, r458 S, r459 S, r200 S, r201 S, r202 S, r460 S, r461 S, r462 S, r463 S, r207 S, r464 S, r209 S, r527 S, r466 S, r467 S, r468 S, r469 S, r470 S, r471 S, r472 S, r473 S, r219 S, r474 S, r475 S, r222 S, r476 S, r224 S, r225 S, r477 S, r478 S, r479 S, r480 S, r481 S, r482 S, r483 S, r484 S, r485 S, r486 S, r487 S, r237 S, r488 S, r239 S, r489 S, r241 S, r490 S, r243 S, r491 S, r492 S, r493 S, r494 S, r495 S, r496 S, r497 S, r498 S, r499 S, r253 S, r254 S, r255 S, r500 S, r501 S, r502 S, r503 S, r260 S, r504 S, r262 S, r505 S, r506 S, r507 S, r508 S, r509 S, r510 S, r511 S, r512 S, r513 S, r514 S, r515 S, r516 S, r528 S, r276 S, r529 S, r519 S, r520 S, r521 S, r281 S, r522 S, r523 S, r524 S, r285 S, r286 S, r530 S]

@[expose] def r531 (S : ℚ) (w : Assignment) : ℚ := (4096 * w 143 * w 143) + (-8192 * w 144 * w 144) + (-1 * w 145)

@[expose] def r532 (S : ℚ) (w : Assignment) : ℚ := (16777216 * w 143 * w 143) + (8192 * w 143 * w 145) + (1 * w 145 * w 145) + (-16777216 * w 146 * w 194)

@[expose] def r533 (S : ℚ) (w : Assignment) : ℚ := (1 * w 145 * w 145) + (-16777216 * w 146 * w 245)

@[expose] def r534 (S : ℚ) (w : Assignment) : ℚ := (1 * w 145 * w 302 * S^1) + (-1 * w 302 * w 308) + (1 * w 309 * w 310)

@[expose] def stage5 (S : ℚ) : List Row := [r290 S, r291 S, r292 S, r293 S, r294 S, r295 S, r296 S, r297 S, r298 S, r299 S, r300 S, r301 S, r302 S, r303 S, r304 S, r305 S, r306 S, r307 S, r308 S, r309 S, r310 S, r311 S, r312 S, r313 S, r314 S, r315 S, r316 S, r317 S, r318 S, r319 S, r320 S, r321 S, r322 S, r323 S, r324 S, r325 S, r326 S, r327 S, r328 S, r329 S, r330 S, r331 S, r332 S, r333 S, r334 S, r335 S, r336 S, r337 S, r338 S, r339 S, r340 S, r341 S, r342 S, r343 S, r344 S, r345 S, r346 S, r347 S, r348 S, r349 S, r350 S, r351 S, r352 S, r353 S, r354 S, r355 S, r356 S, r357 S, r358 S, r69 S, r70 S, r359 S, r360 S, r73 S, r74 S, r361 S, r362 S, r77 S, r78 S, r363 S, r364 S, r365 S, r366 S, r367 S, r368 S, r369 S, r370 S, r371 S, r372 S, r373 S, r374 S, r375 S, r376 S, r377 S, r378 S, r379 S, r380 S, r381 S, r382 S, r383 S, r384 S, r385 S, r386 S, r387 S, r388 S, r389 S, r531 S, r391 S, r392 S, r393 S, r394 S, r111 S, r395 S, r113 S, r396 S, r397 S, r116 S, r117 S, r118 S, r119 S, r398 S, r399 S, r400 S, r401 S, r402 S, r403 S, r404 S, r405 S, r406 S, r407 S, r408 S, r131 S, r409 S, r133 S, r410 S, r135 S, r411 S, r137 S, r412 S, r413 S, r414 S, r415 S, r416 S, r417 S, r418 S, r419 S, r420 S, r147 S, r148 S, r149 S, r421 S, r151 S, r422 S, r423 S, r154 S, r424 S, r156 S, r532 S, r426 S, r427 S, r428 S, r429 S, r430 S, r431 S, r432 S, r433 S, r166 S, r434 S, r435 S, r169 S, r436 S, r171 S, r172 S, r437 S, r438 S, r439 S, r440 S, r441 S, r442 S, r443 S, r444 S, r445 S, r446 S, r447 S, r184 S, r448 S, r186 S, r449 S, r188 S, r450 S, r190 S, r451 S, r452 S, r453 S, r454 S, r455 S, r456 S, r457 S, r458 S, r459 S, r200 S, r201 S, r202 S, r460 S, r461 S, r462 S, r463 S, r207 S, r464 S, r209 S, r533 S, r466 S, r467 S, r468 S, r469 S, r470 S, r471 S, r472 S, r473 S, r219 S, r474 S, r475 S, r222 S, r476 S, r224 S, r225 S, r477 S, r478 S, r479 S, r480 S, r481 S, r482 S, r483 S, r484 S, r485 S, r486 S, r487 S, r237 S, r488 S, r239 S, r489 S, r241 S, r490 S, r243 S, r491 S, r492 S, r493 S, r494 S, r495 S, r496 S, r497 S, r498 S, r499 S, r253 S, r254 S, r255 S, r500 S, r501 S, r502 S, r503 S, r260 S, r504 S, r262 S, r505 S, r506 S, r507 S, r508 S, r509 S, r510 S, r511 S, r512 S, r513 S, r514 S, r515 S, r516 S, r528 S, r276 S, r534 S, r519 S, r520 S, r521 S, r281 S, r522 S, r523 S, r524 S, r285 S, r286 S, r530 S]

@[expose] def stage6 (S : ℚ) : List Row := [r290 S, r291 S, r292 S, r293 S, r294 S, r295 S, r296 S, r297 S, r298 S, r299 S, r300 S, r301 S, r302 S, r303 S, r304 S, r305 S, r306 S, r307 S, r308 S, r309 S, r310 S, r311 S, r312 S, r313 S, r314 S, r315 S, r316 S, r317 S, r318 S, r319 S, r320 S, r321 S, r322 S, r323 S, r324 S, r325 S, r326 S, r327 S, r328 S, r329 S, r330 S, r331 S, r332 S, r333 S, r334 S, r335 S, r336 S, r337 S, r338 S, r339 S, r340 S, r341 S, r342 S, r343 S, r344 S, r345 S, r346 S, r347 S, r348 S, r349 S, r350 S, r351 S, r352 S, r353 S, r354 S, r355 S, r356 S, r357 S, r358 S, r69 S, r70 S, r359 S, r360 S, r73 S, r74 S, r361 S, r362 S, r77 S, r78 S, r363 S, r364 S, r365 S, r366 S, r367 S, r368 S, r369 S, r370 S, r371 S, r372 S, r373 S, r374 S, r375 S, r376 S, r377 S, r378 S, r379 S, r380 S, r381 S, r382 S, r383 S, r384 S, r385 S, r386 S, r387 S, r388 S, r389 S, r531 S, r391 S, r392 S, r393 S, r394 S, r111 S, r395 S, r113 S, r396 S, r397 S, r116 S, r117 S, r118 S, r119 S, r398 S, r399 S, r400 S, r401 S, r402 S, r403 S, r404 S, r405 S, r406 S, r407 S, r408 S, r131 S, r409 S, r133 S, r410 S, r135 S, r411 S, r137 S, r412 S, r413 S, r414 S, r415 S, r416 S, r417 S, r418 S, r419 S, r420 S, r147 S, r148 S, r149 S, r421 S, r151 S, r422 S, r423 S, r154 S, r424 S, r156 S, r532 S, r426 S, r427 S, r428 S, r429 S, r430 S, r431 S, r432 S, r433 S, r166 S, r434 S, r435 S, r169 S, r436 S, r171 S, r172 S, r437 S, r438 S, r439 S, r440 S, r441 S, r442 S, r443 S, r444 S, r445 S, r446 S, r447 S, r184 S, r448 S, r186 S, r449 S, r188 S, r450 S, r190 S, r451 S, r452 S, r453 S, r454 S, r455 S, r456 S, r457 S, r458 S, r459 S, r200 S, r201 S, r202 S, r460 S, r461 S, r462 S, r463 S, r207 S, r464 S, r209 S, r533 S, r466 S, r467 S, r468 S, r469 S, r470 S, r471 S, r472 S, r473 S, r219 S, r474 S, r475 S, r222 S, r476 S, r224 S, r225 S, r477 S, r478 S, r479 S, r480 S, r481 S, r482 S, r483 S, r484 S, r485 S, r486 S, r487 S, r237 S, r488 S, r239 S, r489 S, r241 S, r490 S, r243 S, r491 S, r492 S, r493 S, r494 S, r495 S, r496 S, r497 S, r498 S, r499 S, r253 S, r254 S, r255 S, r500 S, r501 S, r502 S, r503 S, r260 S, r504 S, r262 S, r505 S, r506 S, r507 S, r508 S, r509 S, r510 S, r511 S, r512 S, r513 S, r514 S, r515 S, r516 S, r528 S, r276 S, r534 S, r519 S, r520 S, r521 S, r281 S, r522 S, r523 S, r524 S, r285 S, r286 S, r530 S]

theorem congr0 (S : ℚ) : ∀ q, HasSolution (stage1 S) q ↔ HasSolution (stage0 S) q := by
  apply solutions_congr
  apply constraints_congr
  simp only [stage1, stage0, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r288 S w = (16 : ℚ) * r287 S w := (by unfold r288 r287; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem congr1 (S : ℚ) : ∀ q, HasSolution (stage2 S) q ↔ HasSolution ((stage1 S).map (fun f => f ∘ (AffineAnchor.forward 55 56 57 S))) q := by
  apply solutions_congr
  apply constraints_congr
  simp only [stage2, stage1, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r289 S w = r288 S ((AffineAnchor.forward 55 56 57 S) w) := (by simp only [r289, r288, AffineAnchor.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem congr2 (S : ℚ) : ∀ q, HasSolution (stage3 S) q ↔ HasSolution (stage2 S) q := by
  apply solutions_congr
  apply constraints_congr
  simp only [stage3, stage2, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (by intro w; have h : r290 S w = (-1 : ℚ) * r0 S w := (by unfold r290 r0; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r291 S w = (-1 : ℚ) * r1 S w := (by unfold r291 r1; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r292 S w = (-1 : ℚ) * r2 S w := (by unfold r292 r2; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r293 S w = ((1 / 2) : ℚ) * r3 S w := (by unfold r293 r3; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r294 S w = (-1 : ℚ) * r4 S w := (by unfold r294 r4; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r295 S w = (-1 : ℚ) * r5 S w := (by unfold r295 r5; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r296 S w = (-1 : ℚ) * r6 S w := (by unfold r296 r6; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r297 S w = ((1 / 2) : ℚ) * r7 S w := (by unfold r297 r7; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r298 S w = (-2 : ℚ) * r8 S w := (by unfold r298 r8; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r299 S w = (-1 : ℚ) * r9 S w := (by unfold r299 r9; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r300 S w = (-1 : ℚ) * r10 S w := (by unfold r300 r10; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r301 S w = ((1 / 2) : ℚ) * r11 S w := (by unfold r301 r11; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r302 S w = (-1 : ℚ) * r12 S w := (by unfold r302 r12; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r303 S w = (-1 : ℚ) * r13 S w := (by unfold r303 r13; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r304 S w = (-1 : ℚ) * r14 S w := (by unfold r304 r14; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r305 S w = ((1 / 2) : ℚ) * r15 S w := (by unfold r305 r15; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r306 S w = (-1 : ℚ) * r16 S w := (by unfold r306 r16; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r307 S w = (-1 : ℚ) * r17 S w := (by unfold r307 r17; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r308 S w = (-1 : ℚ) * r18 S w := (by unfold r308 r18; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r309 S w = ((1 / 2) : ℚ) * r19 S w := (by unfold r309 r19; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r310 S w = (-1 : ℚ) * r20 S w := (by unfold r310 r20; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r311 S w = (-1 : ℚ) * r21 S w := (by unfold r311 r21; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r312 S w = (-1 : ℚ) * r22 S w := (by unfold r312 r22; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r313 S w = ((1 / 2) : ℚ) * r23 S w := (by unfold r313 r23; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r314 S w = (-1 : ℚ) * r24 S w := (by unfold r314 r24; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r315 S w = (-1 : ℚ) * r25 S w := (by unfold r315 r25; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r316 S w = (-1 : ℚ) * r26 S w := (by unfold r316 r26; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r317 S w = ((1 / 2) : ℚ) * r27 S w := (by unfold r317 r27; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r318 S w = (-1 : ℚ) * r28 S w := (by unfold r318 r28; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r319 S w = (-1 : ℚ) * r29 S w := (by unfold r319 r29; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r320 S w = (-1 : ℚ) * r30 S w := (by unfold r320 r30; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r321 S w = ((1 / 2) : ℚ) * r31 S w := (by unfold r321 r31; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r322 S w = (-1 : ℚ) * r32 S w := (by unfold r322 r32; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r323 S w = (-1 : ℚ) * r33 S w := (by unfold r323 r33; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r324 S w = (-1 : ℚ) * r34 S w := (by unfold r324 r34; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r325 S w = (-1 : ℚ) * r35 S w := (by unfold r325 r35; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r326 S w = (8 : ℚ) * r36 S w := (by unfold r326 r36; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r327 S w = (8 : ℚ) * r37 S w := (by unfold r327 r37; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r328 S w = (-1 : ℚ) * r38 S w := (by unfold r328 r38; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r329 S w = (-1 : ℚ) * r39 S w := (by unfold r329 r39; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r330 S w = (-1 : ℚ) * r40 S w := (by unfold r330 r40; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r331 S w = (-1 : ℚ) * r41 S w := (by unfold r331 r41; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r332 S w = (-1 : ℚ) * r42 S w := (by unfold r332 r42; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r333 S w = (-1 : ℚ) * r43 S w := (by unfold r333 r43; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r334 S w = (-1 : ℚ) * r44 S w := (by unfold r334 r44; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r335 S w = (-1 : ℚ) * r45 S w := (by unfold r335 r45; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r336 S w = (-1 : ℚ) * r46 S w := (by unfold r336 r46; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r337 S w = (-1 : ℚ) * r47 S w := (by unfold r337 r47; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r338 S w = (-1 : ℚ) * r48 S w := (by unfold r338 r48; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r339 S w = (-1 : ℚ) * r49 S w := (by unfold r339 r49; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r340 S w = (-1 : ℚ) * r50 S w := (by unfold r340 r50; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r341 S w = (-1 : ℚ) * r51 S w := (by unfold r341 r51; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r342 S w = (-1 : ℚ) * r52 S w := (by unfold r342 r52; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r343 S w = (-195 : ℚ) * r53 S w := (by unfold r343 r53; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r344 S w = (-195 : ℚ) * r54 S w := (by unfold r344 r54; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r345 S w = (8 : ℚ) * r55 S w := (by unfold r345 r55; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r346 S w = (-8 : ℚ) * r56 S w := (by unfold r346 r56; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r347 S w = (-195 : ℚ) * r57 S w := (by unfold r347 r57; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r348 S w = (195 : ℚ) * r58 S w := (by unfold r348 r58; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r349 S w = (-195 : ℚ) * r59 S w := (by unfold r349 r59; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r350 S w = (195 : ℚ) * r60 S w := (by unfold r350 r60; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r351 S w = (-195 : ℚ) * r61 S w := (by unfold r351 r61; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r352 S w = (195 : ℚ) * r62 S w := (by unfold r352 r62; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r353 S w = (-8 : ℚ) * r63 S w := (by unfold r353 r63; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r354 S w = (8 : ℚ) * r64 S w := (by unfold r354 r64; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r355 S w = (5 : ℚ) * r65 S w := (by unfold r355 r65; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r356 S w = (-5 : ℚ) * r66 S w := (by unfold r356 r66; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r357 S w = (-8 : ℚ) * r67 S w := (by unfold r357 r67; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r358 S w = (8 : ℚ) * r68 S w := (by unfold r358 r68; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r359 S w = (-8 : ℚ) * r71 S w := (by unfold r359 r71; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r360 S w = (8 : ℚ) * r72 S w := (by unfold r360 r72; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r361 S w = (-8 : ℚ) * r75 S w := (by unfold r361 r75; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r362 S w = (8 : ℚ) * r76 S w := (by unfold r362 r76; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r363 S w = (-1 : ℚ) * r79 S w := (by unfold r363 r79; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r364 S w = (-1 : ℚ) * r80 S w := (by unfold r364 r80; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r365 S w = (-1 : ℚ) * r81 S w := (by unfold r365 r81; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r366 S w = (-1 : ℚ) * r82 S w := (by unfold r366 r82; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r367 S w = (-1 : ℚ) * r83 S w := (by unfold r367 r83; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r368 S w = (-1 : ℚ) * r84 S w := (by unfold r368 r84; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r369 S w = (-2 : ℚ) * r85 S w := (by unfold r369 r85; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r370 S w = (-1 : ℚ) * r86 S w := (by unfold r370 r86; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r371 S w = (-1 : ℚ) * r87 S w := (by unfold r371 r87; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r372 S w = (-1 : ℚ) * r88 S w := (by unfold r372 r88; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r373 S w = (-1 : ℚ) * r89 S w := (by unfold r373 r89; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r374 S w = (-1 : ℚ) * r90 S w := (by unfold r374 r90; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r375 S w = (-1 : ℚ) * r91 S w := (by unfold r375 r91; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r376 S w = (-1 : ℚ) * r92 S w := (by unfold r376 r92; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r377 S w = (-1 : ℚ) * r93 S w := (by unfold r377 r93; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r378 S w = (-1 : ℚ) * r94 S w := (by unfold r378 r94; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r379 S w = (-1 : ℚ) * r95 S w := (by unfold r379 r95; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r380 S w = (-221771664 : ℚ) * r96 S w := (by unfold r380 r96; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r381 S w = (-14892 : ℚ) * r97 S w := (by unfold r381 r97; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r382 S w = (-1 : ℚ) * r98 S w := (by unfold r382 r98; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r383 S w = (-1 : ℚ) * r99 S w := (by unfold r383 r99; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r384 S w = (-1 : ℚ) * r100 S w := (by unfold r384 r100; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r385 S w = (-1 : ℚ) * r101 S w := (by unfold r385 r101; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r386 S w = (-1 : ℚ) * r102 S w := (by unfold r386 r102; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r387 S w = (-1 : ℚ) * r103 S w := (by unfold r387 r103; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r388 S w = (-1 : ℚ) * r104 S w := (by unfold r388 r104; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r389 S w = (-1 : ℚ) * r105 S w := (by unfold r389 r105; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r390 S w = (-1 : ℚ) * r106 S w := (by unfold r390 r106; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r391 S w = (-1 : ℚ) * r107 S w := (by unfold r391 r107; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r392 S w = (-1 : ℚ) * r108 S w := (by unfold r392 r108; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r393 S w = (-1 : ℚ) * r109 S w := (by unfold r393 r109; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r394 S w = (-3081901 : ℚ) * r110 S w := (by unfold r394 r110; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r395 S w = (-1952786 : ℚ) * r112 S w := (by unfold r395 r112; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r396 S w = (-1 : ℚ) * r114 S w := (by unfold r396 r114; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r397 S w = (-1 : ℚ) * r115 S w := (by unfold r397 r115; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r398 S w = (-1 : ℚ) * r120 S w := (by unfold r398 r120; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r399 S w = (-1 : ℚ) * r121 S w := (by unfold r399 r121; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r400 S w = (-1 : ℚ) * r122 S w := (by unfold r400 r122; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r401 S w = (-1 : ℚ) * r123 S w := (by unfold r401 r123; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r402 S w = (-1 : ℚ) * r124 S w := (by unfold r402 r124; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r403 S w = (-1 : ℚ) * r125 S w := (by unfold r403 r125; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r404 S w = (-1 : ℚ) * r126 S w := (by unfold r404 r126; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r405 S w = (-1 : ℚ) * r127 S w := (by unfold r405 r127; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r406 S w = (-1 : ℚ) * r128 S w := (by unfold r406 r128; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r407 S w = (-1 : ℚ) * r129 S w := (by unfold r407 r129; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r408 S w = (-1 : ℚ) * r130 S w := (by unfold r408 r130; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r409 S w = (-1 : ℚ) * r132 S w := (by unfold r409 r132; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r410 S w = (-1 : ℚ) * r134 S w := (by unfold r410 r134; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r411 S w = (-1 : ℚ) * r136 S w := (by unfold r411 r136; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r412 S w = (-1 : ℚ) * r138 S w := (by unfold r412 r138; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r413 S w = (-1 : ℚ) * r139 S w := (by unfold r413 r139; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r414 S w = (-1 : ℚ) * r140 S w := (by unfold r414 r140; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r415 S w = (-1 : ℚ) * r141 S w := (by unfold r415 r141; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r416 S w = (-1 : ℚ) * r142 S w := (by unfold r416 r142; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r417 S w = (-1 : ℚ) * r143 S w := (by unfold r417 r143; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r418 S w = (-1 : ℚ) * r144 S w := (by unfold r418 r144; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r419 S w = (-1 : ℚ) * r145 S w := (by unfold r419 r145; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r420 S w = (-1 : ℚ) * r146 S w := (by unfold r420 r146; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r421 S w = (-2 : ℚ) * r150 S w := (by unfold r421 r150; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r422 S w = (-1 : ℚ) * r152 S w := (by unfold r422 r152; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r423 S w = (-1 : ℚ) * r153 S w := (by unfold r423 r153; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r424 S w = (-3 : ℚ) * r155 S w := (by unfold r424 r155; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r425 S w = (-1 : ℚ) * r157 S w := (by unfold r425 r157; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r426 S w = (-1 : ℚ) * r158 S w := (by unfold r426 r158; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r427 S w = (-1 : ℚ) * r159 S w := (by unfold r427 r159; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r428 S w = (-1205412 : ℚ) * r160 S w := (by unfold r428 r160; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r429 S w = (-1 : ℚ) * r161 S w := (by unfold r429 r161; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r430 S w = (-1 : ℚ) * r162 S w := (by unfold r430 r162; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r431 S w = (-1 : ℚ) * r163 S w := (by unfold r431 r163; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r432 S w = (-1952786 : ℚ) * r164 S w := (by unfold r432 r164; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r433 S w = (-2 : ℚ) * r165 S w := (by unfold r433 r165; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r434 S w = (-1 : ℚ) * r167 S w := (by unfold r434 r167; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r435 S w = (-1 : ℚ) * r168 S w := (by unfold r435 r168; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r436 S w = (-1 : ℚ) * r170 S w := (by unfold r436 r170; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r437 S w = (-1 : ℚ) * r173 S w := (by unfold r437 r173; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r438 S w = (-1 : ℚ) * r174 S w := (by unfold r438 r174; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r439 S w = (-1 : ℚ) * r175 S w := (by unfold r439 r175; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r440 S w = (-1 : ℚ) * r176 S w := (by unfold r440 r176; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r441 S w = (-1 : ℚ) * r177 S w := (by unfold r441 r177; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r442 S w = (-1 : ℚ) * r178 S w := (by unfold r442 r178; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r443 S w = (-1 : ℚ) * r179 S w := (by unfold r443 r179; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r444 S w = (-1 : ℚ) * r180 S w := (by unfold r444 r180; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r445 S w = (-1 : ℚ) * r181 S w := (by unfold r445 r181; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r446 S w = (-1 : ℚ) * r182 S w := (by unfold r446 r182; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r447 S w = (-1 : ℚ) * r183 S w := (by unfold r447 r183; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r448 S w = (-1 : ℚ) * r185 S w := (by unfold r448 r185; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r449 S w = (-1 : ℚ) * r187 S w := (by unfold r449 r187; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r450 S w = (-1 : ℚ) * r189 S w := (by unfold r450 r189; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r451 S w = (-1 : ℚ) * r191 S w := (by unfold r451 r191; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r452 S w = (-1 : ℚ) * r192 S w := (by unfold r452 r192; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r453 S w = (-1 : ℚ) * r193 S w := (by unfold r453 r193; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r454 S w = (-1 : ℚ) * r194 S w := (by unfold r454 r194; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r455 S w = (-1 : ℚ) * r195 S w := (by unfold r455 r195; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r456 S w = (-1 : ℚ) * r196 S w := (by unfold r456 r196; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r457 S w = (-1 : ℚ) * r197 S w := (by unfold r457 r197; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r458 S w = (-1 : ℚ) * r198 S w := (by unfold r458 r198; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r459 S w = (-1 : ℚ) * r199 S w := (by unfold r459 r199; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r460 S w = (-2 : ℚ) * r203 S w := (by unfold r460 r203; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r461 S w = (-1 : ℚ) * r204 S w := (by unfold r461 r204; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r462 S w = (-1 : ℚ) * r205 S w := (by unfold r462 r205; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r463 S w = (-1 : ℚ) * r206 S w := (by unfold r463 r206; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r464 S w = (-3 : ℚ) * r208 S w := (by unfold r464 r208; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r465 S w = (-1 : ℚ) * r210 S w := (by unfold r465 r210; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r466 S w = (-1 : ℚ) * r211 S w := (by unfold r466 r211; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r467 S w = (-1 : ℚ) * r212 S w := (by unfold r467 r212; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r468 S w = (-1205412 : ℚ) * r213 S w := (by unfold r468 r213; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r469 S w = (-1 : ℚ) * r214 S w := (by unfold r469 r214; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r470 S w = (-1 : ℚ) * r215 S w := (by unfold r470 r215; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r471 S w = (-1 : ℚ) * r216 S w := (by unfold r471 r216; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r472 S w = (-1952786 : ℚ) * r217 S w := (by unfold r472 r217; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r473 S w = (-2 : ℚ) * r218 S w := (by unfold r473 r218; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r474 S w = (-1 : ℚ) * r220 S w := (by unfold r474 r220; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r475 S w = (-1 : ℚ) * r221 S w := (by unfold r475 r221; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r476 S w = (-1 : ℚ) * r223 S w := (by unfold r476 r223; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r477 S w = (-1 : ℚ) * r226 S w := (by unfold r477 r226; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r478 S w = (-1 : ℚ) * r227 S w := (by unfold r478 r227; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r479 S w = (-1 : ℚ) * r228 S w := (by unfold r479 r228; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r480 S w = (-1 : ℚ) * r229 S w := (by unfold r480 r229; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r481 S w = (-1 : ℚ) * r230 S w := (by unfold r481 r230; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r482 S w = (-1 : ℚ) * r231 S w := (by unfold r482 r231; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r483 S w = (-1 : ℚ) * r232 S w := (by unfold r483 r232; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r484 S w = (-1 : ℚ) * r233 S w := (by unfold r484 r233; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r485 S w = (-1 : ℚ) * r234 S w := (by unfold r485 r234; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r486 S w = (-1 : ℚ) * r235 S w := (by unfold r486 r235; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r487 S w = (-1 : ℚ) * r236 S w := (by unfold r487 r236; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r488 S w = (-1 : ℚ) * r238 S w := (by unfold r488 r238; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r489 S w = (-1 : ℚ) * r240 S w := (by unfold r489 r240; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r490 S w = (-1 : ℚ) * r242 S w := (by unfold r490 r242; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r491 S w = (-1 : ℚ) * r244 S w := (by unfold r491 r244; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r492 S w = (-1 : ℚ) * r245 S w := (by unfold r492 r245; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r493 S w = (-1 : ℚ) * r246 S w := (by unfold r493 r246; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r494 S w = (-1 : ℚ) * r247 S w := (by unfold r494 r247; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r495 S w = (-1 : ℚ) * r248 S w := (by unfold r495 r248; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r496 S w = (-1 : ℚ) * r249 S w := (by unfold r496 r249; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r497 S w = (-1 : ℚ) * r250 S w := (by unfold r497 r250; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r498 S w = (-1 : ℚ) * r251 S w := (by unfold r498 r251; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r499 S w = (-1 : ℚ) * r252 S w := (by unfold r499 r252; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r500 S w = (-2 : ℚ) * r256 S w := (by unfold r500 r256; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r501 S w = (-1 : ℚ) * r257 S w := (by unfold r501 r257; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r502 S w = (-1 : ℚ) * r258 S w := (by unfold r502 r258; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r503 S w = (-1 : ℚ) * r259 S w := (by unfold r503 r259; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r504 S w = (-3 : ℚ) * r261 S w := (by unfold r504 r261; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r505 S w = (-1 : ℚ) * r263 S w := (by unfold r505 r263; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r506 S w = (-100291113 : ℚ) * r264 S w := (by unfold r506 r264; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r507 S w = (-1 : ℚ) * r265 S w := (by unfold r507 r265; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r508 S w = (-1 : ℚ) * r266 S w := (by unfold r508 r266; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r509 S w = (-1 : ℚ) * r267 S w := (by unfold r509 r267; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r510 S w = (-1 : ℚ) * r268 S w := (by unfold r510 r268; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r511 S w = (-1 : ℚ) * r269 S w := (by unfold r511 r269; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r512 S w = (-1 : ℚ) * r270 S w := (by unfold r512 r270; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r513 S w = (-1 : ℚ) * r271 S w := (by unfold r513 r271; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r514 S w = (-8 : ℚ) * r272 S w := (by unfold r514 r272; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r515 S w = (4 : ℚ) * r273 S w := (by unfold r515 r273; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r516 S w = (-1 : ℚ) * r274 S w := (by unfold r516 r274; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r517 S w = (-1 : ℚ) * r275 S w := (by unfold r517 r275; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r518 S w = (-1 : ℚ) * r277 S w := (by unfold r518 r277; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r519 S w = (-1 : ℚ) * r278 S w := (by unfold r519 r278; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r520 S w = (-1 : ℚ) * r279 S w := (by unfold r520 r279; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r521 S w = (-1 : ℚ) * r280 S w := (by unfold r521 r280; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r522 S w = (-1 : ℚ) * r282 S w := (by unfold r522 r282; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r523 S w = (-1 : ℚ) * r283 S w := (by unfold r523 r283; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (by intro w; have h : r524 S w = (-3 : ℚ) * r284 S w := (by unfold r524 r284; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem congr3 (S : ℚ) : ∀ q, HasSolution (stage4 S) q ↔ HasSolution ((stage3 S).map (fun f => f ∘ (AnchorValueShear.forward 308 145 S))) q := by
  apply solutions_congr
  apply constraints_congr
  simp only [stage4, stage3, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r525 S w = r390 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r525, r390, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r526 S w = r425 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r526, r425, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r527 S w = r465 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r527, r465, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r528 S w = r517 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r528, r517, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r529 S w = r518 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r529, r518, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r530 S w = r289 S ((AnchorValueShear.forward 308 145 S) w) := (by simp only [r530, r289, AnchorValueShear.forward] <;> norm_num <;> ring); simpa only [Function.comp_def, h]) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem congr4 (S : ℚ) : ∀ q, HasSolution (stage5 S) q ↔ HasSolution (stage4 S) q := by
  apply solutions_congr
  apply constraints_congr
  simp only [stage5, stage4, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r531 S w = (4096 : ℚ) * r525 S w := (by unfold r531 r525; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r532 S w = (16777216 : ℚ) * r526 S w := (by unfold r532 r526; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r533 S w = (16777216 : ℚ) * r527 S w := (by unfold r533 r527; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (by intro w; have h : r534 S w = (-1 : ℚ) * r529 S w := (by unfold r534 r529; ring); rw [h]; exact mul_eq_zero.trans (by norm_num)) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem congr5 (S : ℚ) : ∀ q, HasSolution (stage6 S) q ↔ HasSolution (stage5 S) q := by
  apply solutions_congr
  apply constraints_congr
  simp only [stage6, stage5, List.map_cons, List.map_nil]
  exact List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.cons (fun _ => Iff.rfl) (
List.Forall₂.nil))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))


theorem source_iff_final (S q : ℚ) : HasSolution (stage0 S) q ↔ HasSolution (stage6 S) q := by
  exact ((congr0 S q).symm).trans (((AffineAnchor.solutions (stage1 S) 55 56 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) S q).trans (congr1 S q).symm).trans (((congr2 S q).symm).trans (((AnchorValueShear.solutions (stage3 S) 308 145 (by decide) (by decide) (by decide) S q).trans (congr3 S q).symm).trans (((congr4 S q).symm).trans (((congr5 S q).symm))))))


end Raw318FinalReplay
