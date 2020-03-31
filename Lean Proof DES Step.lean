variable data : Type

variables 
L15_E R15_E L16_E R16_E 
L0_D  R0_D  L1_D  R1_D 
K_16                    : data

variable xor (d1 d2 : data) : data
variable f (d k : data) : data

premise xor_assoc (x1 x2 x3 : data) :
(xor (xor x1 x2) x3) = (xor x1 (xor x2 x3))

premise xor_cancel : ∀ x1 x2 : data, xor x1 (xor x2 x2) = x1

premise H1        : L16_E = R15_E
premise H2        : R16_E = xor L15_E (f R15_E K_16)
premise H3        : L0_D  = R16_E
premise H4        : R0_D  = L16_E
premise H5        : L1_D  = R0_D
premise H6        : R1_D  = xor L0_D (f R0_D K_16)

theorem ProofRight_Long : R15_E = L1_D :=
have H7  : R15_E = L16_E, from eq.symm  H1,
have H8  : L16_E = R0_D,  from eq.symm  H4,
have H9  : R0_D  = L1_D,  from eq.symm  H5,
have H10 : R15_E = R0_D,  from eq.trans H7  H8,
show       R15_E = L1_D,  from eq.trans H10 H9

theorem ProofLeft : L15_E = R1_D :=
have H11 : R1_D = xor L0_D  (f R0_D  K_16), from H6,
have H12 : R1_D = xor R16_E (f R0_D  K_16), from eq.subst H3 H11,
have H13 : R1_D = xor R16_E (f L16_E K_16), from eq.subst H4 H12,
have H14 : R1_D = xor R16_E (f R15_E K_16), from eq.subst H1 H13,
have H15 : R1_D = xor (xor L15_E (f R15_E K_16)) (f R15_E K_16),
    from eq.subst H2 H14,
have H16 : xor (xor L15_E (f R15_E K_16)) (f R15_E K_16) = 
           xor L15_E (xor (f R15_E K_16) (f R15_E K_16)),
    from xor_assoc L15_E (f R15_E K_16) (f R15_E K_16),
have H17 : R1_D = xor L15_E (xor (f R15_E K_16) (f R15_E K_16)),
    from eq.trans H15 H16,
have H18 : xor L15_E (xor (f R15_E K_16) (f R15_E K_16)) = L15_E,
    from xor_cancel L15_E (f R15_E K_16),
show L15_E = R1_D, from eq.symm (eq.trans H17 H18)
