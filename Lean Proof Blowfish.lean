variable data : Type

variables
L0  L1  L2  L3  L4  L5  L6  L7  L8
L9  L10 L11 L12 L13 L14 L15 L16

R0  R1  R2  R3  R4  R5  R6  R7  R8
R9  R10 R11 R12 R13 R14 R15 R16

L0_D  L1_D  L2_D  L3_D  L4_D  L5_D  L6_D  L7_D  L8_D
L9_D  L10_D L11_D L12_D L13_D L14_D L15_D L16_D

R0_D  R1_D  R2_D  R3_D  R4_D  R5_D  R6_D  R7_D  R8_D
R9_D  R10_D R11_D R12_D R13_D R14_D R15_D R16_D

P1  P2  P3  P4  P5  P6  P7  P8  P9
P10 P11 P12 P13 P14 P15 P16 P17 P18        : data

variable xor (d1 d2 : data) : data
variable F (d : data) : data

definition StepLeft (l r p : data) : data :=
xor r (F (xor l p))

definition StepRight (l r p : data) : data :=
xor l p

definition StepLeftFinal (l r p : data) : data :=
xor r (F (xor l p))

definition StepRightFinal (l r p : data) : data :=
xor l p

premise xor_comm  (x1 x2 : data) :
(xor x1 x2) = (xor x2 x1)

premise xor_assoc (x1 x2 x3 : data) :
(xor (xor x1 x2) x3) = (xor x1 (xor x2 x3))

premise xor_cancel : ∀ x1 x2 : data, xor x1 (xor x2 x2) = x1

premise xor_swap : ∀ x1 x2 x3 : data, x1 = xor x2 x3 → x2 = xor x1 x3

premise L1_Def        : L1  = xor R0  (F (xor L0 P1))
premise R1_Def        : R1  = xor L0  P1
premise L2_Def        : L2  = xor R1  (F (xor L1 P2))
premise R2_Def        : R2  = xor L1  P2
premise L3_Def        : L3  = xor R2  (F (xor L2 P3))
premise R3_Def        : R3  = xor L2  P3
premise L4_Def        : L4  = xor R3  (F (xor L3 P4))
premise R4_Def        : R4  = xor L3  P4
premise L5_Def        : L5  = xor R4  (F (xor L4 P5))
premise R5_Def        : R5  = xor L4  P5
premise L6_Def        : L6  = xor R5  (F (xor L5 P6))
premise R6_Def        : R6  = xor L5  P6
premise L7_Def        : L7  = xor R6  (F (xor L6 P7))
premise R7_Def        : R7  = xor L6  P7
premise L8_Def        : L8  = xor R7  (F (xor L7 P8))
premise R8_Def        : R8  = xor L7  P8
premise L9_Def        : L9  = xor R8  (F (xor L8 P9))
premise R9_Def        : R9  = xor L8  P9
premise L10_Def       : L10 = xor R9  (F (xor L9 P10))
premise R10_Def       : R10 = xor L9  P10
premise L11_Def       : L11 = xor R10 (F (xor L10 P11))
premise R11_Def       : R11 = xor L10 P11
premise L12_Def       : L12 = xor R11 (F (xor L11 P12))
premise R12_Def       : R12 = xor L11 P12
premise L13_Def       : L13 = xor R12 (F (xor L12 P13))
premise R13_Def       : R13 = xor L12 P13
premise L14_Def       : L14 = xor R13 (F (xor L13 P14))
premise R14_Def       : R14 = xor L13 P14
premise L15_Def       : L15 = xor R14 (F (xor L14 P15))
premise R15_Def       : R15 = xor L14 P15
premise L16_Def       : L16 = xor P18 (xor L15 P16)
premise R16_Def       : R16 = xor P17 (xor R15 (F (xor L15 P16)))

premise L0_D_Def      : L0_D  = L16
premise R0_D_Def      : R0_D  = R16
premise L1_D_Def      : L1_D  = xor R0_D  (F (xor L0_D P18))
premise R1_D_Def      : R1_D  = xor L0_D  P18
premise L2_D_Def      : L2_D  = xor R1_D  (F (xor L1_D P17))
premise R2_D_Def      : R2_D  = xor L1_D  P17
premise L3_D_Def      : L3_D  = xor R2_D  (F (xor L2_D P16))
premise R3_D_Def      : R3_D  = xor L2_D  P16
premise L4_D_Def      : L4_D  = xor R3_D  (F (xor L3_D P15))
premise R4_D_Def      : R4_D  = xor L3_D  P15
premise L5_D_Def      : L5_D  = xor R4_D  (F (xor L4_D P14))
premise R5_D_Def      : R5_D  = xor L4_D  P14
premise L6_D_Def      : L6_D  = xor R5_D  (F (xor L5_D P13))
premise R6_D_Def      : R6_D  = xor L5_D  P13
premise L7_D_Def      : L7_D  = xor R6_D  (F (xor L6_D P12))
premise R7_D_Def      : R7_D  = xor L6_D  P12
premise L8_D_Def      : L8_D  = xor R7_D  (F (xor L7_D P11))
premise R8_D_Def      : R8_D  = xor L7_D  P11
premise L9_D_Def      : L9_D  = xor R8_D  (F (xor L8_D P10))
premise R9_D_Def      : R9_D  = xor L8_D  P10
premise L10_D_Def     : L10_D = xor R9_D  (F (xor L9_D P9))
premise R10_D_Def     : R10_D = xor L9_D  P9
premise L11_D_Def     : L11_D = xor R10_D (F (xor L10_D P8))
premise R11_D_Def     : R11_D = xor L10_D P8
premise L12_D_Def     : L12_D = xor R11_D (F (xor L11_D P7))
premise R12_D_Def     : R12_D = xor L11_D P7
premise L13_D_Def     : L13_D = xor R12_D (F (xor L12_D P6))
premise R13_D_Def     : R13_D = xor L12_D P6
premise L14_D_Def     : L14_D = xor R13_D (F (xor L13_D P5))
premise R14_D_Def     : R14_D = xor L13_D P5
premise L15_D_Def     : L15_D = xor R14_D (F (xor L14_D P4))
premise R15_D_Def     : R15_D = xor L14_D P4
premise L16_D_Def     : L16_D = xor P1 (xor L15_D P3)
premise R16_D_Def     : R16_D = xor P2 (xor R15_D (F (xor L15_D P3)))

theorem ProofL1 : L1_D = xor P17 R15, :=
have H1  : L1_D = xor R0_D (F (xor L0_D P18)), from L1_D_Def,
have H2  : L1_D = xor R16  (F (xor L0_D P18)),
    from eq.subst R0_D_Def H1,
have H3  : L1_D = xor R16  (F (xor L16 P18)),
    from eq.subst L0_D_Def H2,
have H4  : L1_D = xor R16  (F (xor (xor P18 (xor L15 P16)) P18)),
    from eq.subst L16_Def H3,
have H5  : L1_D = xor R16  (F (xor (xor (xor L15 P16) P18) P18)),
    from eq.subst (xor_comm P18 (xor L15 P16)) H4,
have H6  : L1_D = xor R16  (F (xor (xor L15 P16) (xor P18 P18))),
    from eq.subst (xor_assoc (xor L15 P16) P18 P18) H5,
have H7  : L1_D = xor R16  (F (xor L15 P16)),
    from eq.subst (xor_cancel (xor L15 P16) P18) H6,
have H8  : L1_D = xor (xor P17 (xor R15 (F (xor L15 P16))))
                      (F (xor L15 P16)),
    from eq.subst R16_Def H7,
have H9  : L1_D = xor P17 (xor (xor R15 (F (xor L15 P16)))
                               (F (xor L15 P16))          ),
    from eq.subst (xor_assoc P17
                             (xor R15 (F (xor L15 P16)))
                             ((F (xor L15 P16)))
                  ) H8,
have H10 : L1_D = xor P17 (xor R15 (xor (F (xor L15 P16))
                                        (F (xor L15 P16)))),
    from eq.subst (xor_assoc R15
                             (F (xor L15 P16))
                             (F (xor L15 P16))
                  ) H9,
show       L1_D = xor P17 R15,
    from eq.subst (xor_cancel R15 (F (xor L15 P16))) H10

theorem ProofR1 : R1_D = xor L15 P16 :=
have H1  : R1_D = xor L0_D P18, from R1_D_Def,
have H2  : R1_D = xor L16  P18, from eq.subst L0_D_Def H1,
have H3  : R1_D = xor (xor P18 (xor L15 P16)) P18,
    from eq.subst L16_Def H2,
have H4  : R1_D = xor (xor (xor L15 P16) P18) P18,
    from eq.subst (xor_comm P18 (xor L15 P16)) H3,
have H5  : R1_D = xor (xor L15 P16) (xor P18 P18),
    from eq.subst (xor_assoc (xor L15 P16) P18 P18) H4,
have H6  : R1_D = xor (xor L15 P16) (xor P18 P18),
    from eq.subst (xor_assoc (xor L15 P16) P18 P18) H5,
show       R1_D = xor L15 P16,
    from eq.subst (xor_cancel (xor L15 P16) P18) H6

theorem ProofStep2
(S1_L : L1_D = xor P17 R15) (S1_R : R1_D = xor L15 P16) :
(L2_D = xor (xor L15 P16) (F R15)) ∧ (R2_D = R15) :=
have H1  : R2_D = xor L1_D P17, from R2_D_Def,
have H2  : R2_D = xor (xor P17 R15) P17, from eq.subst S1_L H1,
have H3  : R2_D = xor (xor R15 P17) P17,
    from eq.subst (xor_comm P17 R15) H2,
have H4  : R2_D = xor R15 (xor P17 P17),
    from eq.subst (xor_assoc R15 P17 P17) H3,
have H5  : R2_D = R15,
    from eq.subst (xor_cancel R15 P17) H4,
have H6  : L2_D = xor R1_D (F (xor L1_D P17)), from L2_D_Def,
have H7  : L2_D = xor R1_D (F R2_D),
    from eq.subst (eq.symm H1) H6,
have H8  : L2_D = xor R1_D (F R15),
    from eq.subst H5 H7,
have H9  : L2_D = xor (xor L15 P16) (F R15),
    from eq.subst S1_R H8,
show       (L2_D = xor (xor L15 P16) (F R15)) ∧ (R2_D = R15),
    from and.intro H9 H5

theorem ProofStep3
(S2_L : L2_D = xor (xor L15 P16) (F R15)) (S2_R : R2_D = R15) :
(L3_D = xor R13 P15) ∧ (R3_D = R14) :=
have H1  : R3_D = xor L2_D P16, from R3_D_Def,
have H2  : R3_D = xor (xor (xor L15 P16) (F R15)) P16,
    from eq.subst S2_L H1,
have H3  : R3_D = xor (xor (F R15) (xor L15 P16)) P16,
    from eq.subst (xor_comm (xor L15 P16) (F R15)) H2,
have H4  : R3_D = xor (F R15) (xor (xor L15 P16) P16),
    from eq.subst (xor_assoc (F R15) (xor L15 P16) P16) H3,
have H5  : R3_D = xor (F R15) (xor L15 (xor P16 P16)),
    from eq.subst (xor_assoc L15 P16 P16) H4,
have H6  : R3_D = xor (F R15) L15,
    from eq.subst (xor_cancel L15 P16) H5,
have H7  : L15 = xor R14 (F R15),
    from eq.subst (eq.symm R15_Def) L15_Def,
have H8  : R14 = xor L15 (F R15),
    from (xor_swap L15 R14 (F R15)) H7,
have H9  : R14 = xor (F R15) L15,
    from eq.subst (xor_comm L15 (F R15)) H8,
have H10 : R3_D = R14,
    from eq.trans H6 (eq.symm H9),
have H11 : L3_D = xor R15 (F (xor L2_D P16)),
    from eq.subst S2_R L3_D_Def,
have H12 : L3_D = xor R15 (F R3_D),
    from eq.subst (eq.symm H1) H11,
have H13 : L3_D = xor R15 (F R14),
    from eq.subst H10 H12,
have H14 : L3_D = xor (xor L14 P15) (F R14),
    from eq.subst R15_Def H13,
have H15 : L3_D = xor (xor L14 P15) (F (xor L13 P14)),
    from eq.subst R14_Def H14,
have H16 : L3_D = xor (xor P15 L14) (F (xor L13 P14)),
    from eq.subst (xor_comm L14 P15) H15,
have H17 : L3_D = xor P15 (xor L14 (F (xor L13 P14))),
    from eq.subst (xor_assoc P15 L14 (F (xor L13 P14))) H16,
have H18 : R13 = xor L14 (F (xor L13 P14)),
    from (xor_swap L14 R13 (F (xor L13 P14))) L14_Def,
have H19 : L3_D = xor P15 R13,
    from eq.subst (eq.symm H18) H17,
have H20 : L3_D = xor R13 P15,
    from eq.subst (xor_comm P15 R13) H19,
show       (L3_D = xor R13 P15) ∧ (R3_D = R14),
    from and.intro H20 H10

theorem ProofStep4
(S3_R : L3_D = xor R13 P15) (S3_L : R3_D = R14) :
(L4_D = xor R12 P14) ∧ (R4_D = R13) :=
have H1  : R4_D = xor L3_D P15,
    from R4_D_Def,
have H2  : R4_D = xor (xor R13 P15) P15,
    from eq.subst S3_R H1,
have H3  : R4_D = xor R13 (xor P15 P15),
    from eq.subst (xor_assoc R13 P15 P15) H2,
have H5  : R4_D = R13,
    from eq.subst (xor_cancel R13 P15) H3,
have H6  : R13 = xor L3_D P15,
    from eq.trans (eq.symm H5) H1,
have H7  : L4_D = xor R3_D (F (xor L3_D P15)),
    from L4_D_Def,
have H8  : L4_D = xor R14 (F (xor L3_D P15)),
    from eq.subst S3_L H7,
have H9  : L4_D = xor R14 (F R13),
    from eq.subst (eq.symm H6) H8,
have H10 : L4_D = xor (xor L13 P14) (F R13),
    from eq.subst R14_Def H9,
have H11 : L4_D = xor (xor P14 L13) (F R13),
    from eq.subst (xor_comm  L13 P14) H10,
have H12 : L4_D = xor P14 (xor L13 (F R13)),
    from eq.subst (xor_assoc P14 L13 (F R13)) H11,
have H13 : L4_D = xor P14 (xor (xor R12 (F (xor L12 P13))) (F R13)),
    from eq.subst L13_Def H12,
have H14 : L4_D = xor P14 (xor R12 (xor (F (xor L12 P13)) (F R13))),
    from eq.subst (xor_assoc R12 (F (xor L12 P13)) (F R13)) H13,
have H15 : L4_D = xor P14 (xor R12 (xor (F (xor L12 P13))
                                        (F (xor L12 P13)))),
    from eq.subst R13_Def H14,
have H16 : L4_D = xor P14 R12,
    from eq.subst (xor_cancel R12 (F (xor L12 P13))) H15,
have H17 : L4_D = xor R12 P14,
    from eq.subst (xor_comm P14 R12) H16,
show       (L4_D = xor R12 P14) ∧ (R4_D = R13),
    from and.intro H17 H5

theorem ProofStep5Left
(S3_R : L15_D = xor R1 P3) (S3_L : R15_D = R2) :
L16_D = L0 :=
have H1  : L16_D = xor P1 (xor L15_D P3),
    from L16_D_Def,
have H2  : L16_D = xor P1 (xor (xor R1 P3) P3),
    from eq.subst S3_R H1,
have H3  : L16_D = xor P1 (xor R1 (xor P3 P3)),
    from eq.subst (xor_assoc R1 P3 P3) H2,
have H4  : L16_D = xor P1 R1,
    from eq.subst (xor_cancel R1 P3) H3,
have H5  : L16_D = xor P1 (xor L0 P1),
    from eq.subst R1_Def H4,
have H6  : L16_D = xor (xor L0 P1) P1,
    from eq.subst (xor_comm P1 (xor L0 P1)) H5,
have H7  : L16_D = xor L0 (xor P1 P1),
    from eq.subst (xor_assoc L0 P1 P1) H6,
show       L16_D = L0,
    from eq.subst (xor_cancel L0 P1) H7

theorem ProofStep5Right
(S3_R : L15_D = xor R1 P3) (S3_L : R15_D = R2) :
R16_D = R0 :=
have H1  : R16_D = xor P2 (xor R15_D (F (xor L15_D P3))),
    from R16_D_Def,
have H2  : R16_D = xor P2 (xor R15_D (F (xor (xor R1 P3) P3))),
    from eq.subst S3_R H1,
have H3  : R16_D = xor P2 (xor R15_D (F (xor R1 (xor P3 P3)))),
    from eq.subst (xor_assoc R1 P3 P3) H2,
have H4  : R16_D = xor P2 (xor R15_D (F R1)),
    from eq.subst (xor_cancel R1 P3) H3,
have H5  : R16_D = xor P2 (xor R2 (F R1)),
    from eq.subst S3_L H4,
have H6  : R16_D = xor P2 (xor R2 (F (xor L0 P1))),
    from eq.subst R1_Def H5,
have H7  : R16_D = xor P2 (xor (xor L1 P2) (F (xor L0 P1))),
    from eq.subst R2_Def H6,
have H8  : R16_D = xor P2 (xor (xor P2 L1) (F (xor L0 P1))),
    from eq.subst (xor_comm L1 P2) H7,
have H9  : R16_D = xor P2 (xor P2 (xor L1 (F (xor L0 P1)))),
    from eq.subst (xor_assoc P2 L1 (F (xor L0 P1))) H8,
have H10 : R16_D = xor (xor P2 P2) (xor L1 (F (xor L0 P1))),
    from eq.subst
        (eq.symm (xor_assoc P2 P2 (xor L1 (F (xor L0 P1))))) H9,
have H11 : R16_D = xor (xor L1 (F (xor L0 P1))) (xor P2 P2),
    from eq.subst
        (xor_comm (xor P2 P2) (xor L1 (F (xor L0 P1)))) H10,
have H12 : R16_D = (xor L1 (F (xor L0 P1))),
    from eq.subst
        (xor_cancel (xor L1 (F (xor L0 P1))) P2) H11,
have H13 : R16_D = (xor (xor R0 (F (xor L0 P1))) (F (xor L0 P1))),
    from eq.subst L1_Def H12,
have H14 : R16_D = (xor R0 (xor (F (xor L0 P1)) (F (xor L0 P1)))),
    from eq.subst (xor_assoc R0 (F (xor L0 P1)) (F (xor L0 P1))) H13,
show       R16_D = R0,
    from eq.subst (xor_cancel R0 (F (xor L0 P1))) H14
