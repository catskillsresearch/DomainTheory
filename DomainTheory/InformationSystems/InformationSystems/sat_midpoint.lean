/-ai
The midpoint of the endpoints of a strict integer interval, taken in the rationals, satisfies that interval token.

Two is positive as a rational, and the strict inequality of the integer endpoints casts to the rationals. The lower comparison rewrites, by positivity of the divisor, as twice the lower endpoint being below the sum of the endpoints, and the cast inequality closes it. The upper comparison likewise rewrites as the sum being below twice the upper endpoint, and the same inequality closes it.
ai-/
module

public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
import all Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid25.Token
public import DomainTheory.InformationSystems.InformationSystems.instDecidableEq
public import DomainTheory.InformationSystems.InformationSystems.Sat

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid25

/-- Midpoint witness: `lo < hi` (on `ℕ`) implies `(lo+hi)/2` lies in `(lo, hi)` on `ℚ`. -/
theorem sat_midpoint {lo hi : ℕ} (hlt : lo < hi) :
    Sat (((lo : ℚ) + (hi : ℚ)) / 2) (.interval lo hi hlt) := by
  have h2 : (0 : ℚ) < 2 := by norm_num
  have _hlo : (lo : ℚ) < (hi : ℚ) := Nat.cast_lt.mpr hlt
  constructor
  · -- lo < (lo+hi)/2 ↔ 2*lo < lo+hi ↔ lo < hi
    rw [lt_div_iff₀ h2]
    linarith
  · rw [div_lt_iff₀ h2]
    linarith

end Factoid25

end DomainTheory.InformationSystems
