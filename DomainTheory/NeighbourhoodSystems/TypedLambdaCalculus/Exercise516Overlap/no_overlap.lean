/-ai
No overlap of any period occurs at any offset in the Thue–Morse bit sequence.

The argument is strong induction on the period. An overlap supplies the period relations and a period at least 1, and the period is even or odd. If the period is twice q, then q is at least 1. An even offset reduces the even positions, by the even recurrence, to an overlap of period q, and an odd offset does the same after the odd recurrence and cancellation of the two negations; either contradicts the inductive hypothesis. If the period is one more than twice q and q is zero, the relations at steps 0 and 1 contradict the absence of three consecutive equal bits. If the offset is even and q is positive, the relations at steps 0 through 3 rewrite by the even and odd recurrences and contradict the absence of three consecutive equal bits, by cases on the bits involved. If the offset is odd and q is 1, the relations at steps 0 through 3 are impossible by cases on the four bits. If the offset is odd and q is at least 2, the relations at steps 1 through 4 likewise contradict the absence of three consecutive equal bits.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516ThueMorse
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.Basic
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.no_three_consec
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.tm_of_eq_two_mul
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise516Overlap.tm_of_eq_two_mul_add_one

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise516

open DomainTheory.NeighbourhoodSystems





/-- **Overlap-freeness of the Thue–Morse sequence** (Scott 1981, PRG-19; Thue 1912). No overlap
exists at any offset and period. -/
theorem no_overlap (p : ℕ) : ∀ i, ¬ Overlap i p := by
  induction p using Nat.strong_induction_on with
  | _ p IH =>
    intro i hov
    obtain ⟨hp1, hrel⟩ := hov
    obtain ⟨q, hq | hq⟩ := Nat.even_or_odd' p
    · -- Even period `p = 2q`: contract to a period-`q` overlap.
      subst hq
      have hq1 : 1 ≤ q := by omega
      obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
      · -- `i = 2a`: even positions give `tm (a+c) = tm (a+q+c)`.
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul (show i + 2 * c = 2 * (a + c) by omega),
          tm_of_eq_two_mul (show i + 2 * q + 2 * c = 2 * (a + q + c) by omega)] at this
        exact this
      · -- `i = 2a+1`: odd positions give `tm (a+c) = tm (a+q+c)` after stripping the `¬`.
        refine IH q (by omega) a ⟨hq1, fun c hc => ?_⟩
        have hk : 2 * c ≤ 2 * q := by omega
        have := hrel (2 * c) hk
        rw [tm_of_eq_two_mul_add_one (show i + 2 * c = 2 * (a + c) + 1 by omega),
          tm_of_eq_two_mul_add_one (show i + 2 * q + 2 * c = 2 * (a + q + c) + 1 by omega)] at this
        exact Bool.not_inj this
    · -- Odd period `p = 2q+1`.
      subst hq
      rcases Nat.eq_zero_or_pos q with rfl | hq1
      · -- `p = 1`: three consecutive equal symbols.
        refine no_three_consec i ⟨?_, ?_⟩
        · have := hrel 0 (by omega); simpa using this
        · have := hrel 1 (by omega); simpa [show i + 1 + 1 = i + 2 by omega] using this
      · -- `p = 2q+1 ≥ 3`.
        obtain ⟨a, hi | hi⟩ := Nat.even_or_odd' i
        · -- `i = 2a`: relations at `k = 0,1,2,3` give a run of three equal symbols at `a+q`.
          subst hi
          have r0 := hrel 0 (by omega)
          have r1 := hrel 1 (by omega)
          have r2 := hrel 2 (by omega)
          have r3 := hrel 3 (by omega)
          rw [tm_of_eq_two_mul (show 2 * a + 0 = 2 * a by omega),
            tm_of_eq_two_mul_add_one (show 2 * a + (2 * q + 1) + 0 = 2 * (a + q) + 1 by omega)] at r0
          rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 = 2 * a + 1 by omega),
            tm_of_eq_two_mul (show 2 * a + (2 * q + 1) + 1 = 2 * (a + q + 1) by omega)] at r1
          rw [tm_of_eq_two_mul (show 2 * a + 2 = 2 * (a + 1) by omega),
            tm_of_eq_two_mul_add_one
              (show 2 * a + (2 * q + 1) + 2 = 2 * (a + q + 1) + 1 by omega)] at r2
          rw [tm_of_eq_two_mul_add_one (show 2 * a + 3 = 2 * (a + 1) + 1 by omega),
            tm_of_eq_two_mul (show 2 * a + (2 * q + 1) + 3 = 2 * (a + q + 2) by omega)] at r3
          refine no_three_consec (a + q) ⟨?_, ?_⟩
          · revert r0 r1; cases tm a <;> cases tm (a + q) <;> cases tm (a + q + 1) <;>
              simp_all
          · revert r1 r2 r3
            cases tm (a + 1) <;> cases tm (a + q + 1) <;> cases tm (a + q + 2) <;> cases tm a <;>
              simp_all
        · -- `i = 2a+1`.
          subst hi
          rcases Nat.eq_or_lt_of_le hq1 with hq2 | hq2
          · -- `q = 1`, i.e. `p = 3`: a direct contradiction from the four relations.
            subst hq2
            have r0 := hrel 0 (by omega)
            have r1 := hrel 1 (by omega)
            have r2 := hrel 2 (by omega)
            have r3 := hrel 3 (by omega)
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 0 = 2 * a + 1 by omega),
              tm_of_eq_two_mul (show 2 * a + 1 + (2 * 1 + 1) + 0 = 2 * (a + 2) by omega)] at r0
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 1 = 2 * (a + 1) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * 1 + 1) + 1 = 2 * (a + 2) + 1 by omega)] at r1
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega),
              tm_of_eq_two_mul (show 2 * a + 1 + (2 * 1 + 1) + 2 = 2 * (a + 3) by omega)] at r2
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 3 = 2 * (a + 2) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * 1 + 1) + 3 = 2 * (a + 3) + 1 by omega)] at r3
            revert r0 r1 r2 r3
            cases tm a <;> cases tm (a + 1) <;> cases tm (a + 2) <;> cases tm (a + 3) <;> simp_all
          · -- `q ≥ 2`, i.e. `p ≥ 5`: relations at `k = 1,2,3,4` give a run of three at `a+q+1`.
            have r1 := hrel 1 (by omega)
            have r2 := hrel 2 (by omega)
            have r3 := hrel 3 (by omega)
            have r4 := hrel 4 (by omega)
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 1 = 2 * (a + 1) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * q + 1) + 1 = 2 * (a + q + 1) + 1 by omega)] at r1
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 2 = 2 * (a + 1) + 1 by omega),
              tm_of_eq_two_mul
                (show 2 * a + 1 + (2 * q + 1) + 2 = 2 * (a + q + 2) by omega)] at r2
            rw [tm_of_eq_two_mul (show 2 * a + 1 + 3 = 2 * (a + 2) by omega),
              tm_of_eq_two_mul_add_one
                (show 2 * a + 1 + (2 * q + 1) + 3 = 2 * (a + q + 2) + 1 by omega)] at r3
            rw [tm_of_eq_two_mul_add_one (show 2 * a + 1 + 4 = 2 * (a + 2) + 1 by omega),
              tm_of_eq_two_mul
                (show 2 * a + 1 + (2 * q + 1) + 4 = 2 * (a + q + 3) by omega)] at r4
            refine no_three_consec (a + q + 1) ⟨?_, ?_⟩
            · revert r1 r2; cases tm (a + 1) <;> cases tm (a + q + 1) <;> cases tm (a + q + 2) <;>
                simp_all
            · revert r3 r4; cases tm (a + 2) <;> cases tm (a + q + 2) <;> cases tm (a + q + 3) <;>
                simp_all

end DomainTheory.NeighbourhoodSystems.Exercise516
