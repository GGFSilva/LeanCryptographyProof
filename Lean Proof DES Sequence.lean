variable L  (n : nat) : data
variable R  (n : nat) : data
variable Ld (n : nat) : data
variable Rd (n : nat) : data

premise BaseLeft  : Ld 0 = R 16
premise BaseRight : Rd 0 = L 16
premise StepLeft  : ∀ i : nat, Ld i = R (16 - i) → Ld (i + 1) = R (16 - (i + 1))
premise StepRight : ∀ i : nat, Rd i = L (16 - i) → Rd (i + 1) = L (16 - (i + 1))

theorem ProofLeft : Ld 16 = R 0 := 
have  H0 : Ld   0      = R  16,              from  BaseLeft, 
have  H1 : Ld ( 0 + 1) = R (16 - ( 0 + 1)), from (StepLeft  0)  H0,
have  H2 : Ld ( 1 + 1) = R (16 - ( 1 + 1)), from (StepLeft  1)  H1,
have  H3 : Ld ( 2 + 1) = R (16 - ( 2 + 1)), from (StepLeft  2)  H2,
have  H4 : Ld ( 3 + 1) = R (16 - ( 3 + 1)), from (StepLeft  3)  H3,
have  H5 : Ld ( 4 + 1) = R (16 - ( 4 + 1)), from (StepLeft  4)  H4,
have  H6 : Ld ( 5 + 1) = R (16 - ( 5 + 1)), from (StepLeft  5)  H5,
have  H7 : Ld ( 6 + 1) = R (16 - ( 6 + 1)), from (StepLeft  6)  H6,
have  H8 : Ld ( 7 + 1) = R (16 - ( 7 + 1)), from (StepLeft  7)  H7,
have  H9 : Ld ( 8 + 1) = R (16 - ( 8 + 1)), from (StepLeft  8)  H8,
have H10 : Ld ( 9 + 1) = R (16 - ( 9 + 1)), from (StepLeft  9)  H9,
have H11 : Ld (10 + 1) = R (16 - (10 + 1)), from (StepLeft 10) H10,
have H12 : Ld (11 + 1) = R (16 - (11 + 1)), from (StepLeft 11) H11,
have H13 : Ld (12 + 1) = R (16 - (12 + 1)), from (StepLeft 12) H12,
have H14 : Ld (13 + 1) = R (16 - (13 + 1)), from (StepLeft 13) H13,
have H15 : Ld (14 + 1) = R (16 - (14 + 1)), from (StepLeft 14) H14,
have H16 : Ld (15 + 1) = R (16 - (15 + 1)), from (StepLeft 15) H15, 
show Ld 16 = R 0, from H16 
