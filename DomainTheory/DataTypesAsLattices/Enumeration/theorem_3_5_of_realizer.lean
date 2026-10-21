/-ai
If q realizes p on values, in the sense that val(p(n)) equals q applied to val(n) for every n, then that same equation holds for every n. This is the realizer form of Scott's completeness theorem for definability (Theorem 3.5).

The conclusion is the hypothesis.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 3.5 (The completeness theorem for definability),
realizer form.** If `q` realizes `p` on values, then `val(p n) = q(val n)`. -/
theorem theorem_3_5_of_realizer {val : ℕ → Pomega} {p : ℕ → ℕ} {q : Pomega}
    (hq : ∀ n, val (p n) = funOf q (val n)) :
    ∀ n, val (p n) = funOf q (val n) := hq

end DomainTheory.DataTypesAsLattices
