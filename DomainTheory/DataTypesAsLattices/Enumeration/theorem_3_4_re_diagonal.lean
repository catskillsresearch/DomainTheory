/-ai
If val(v(k)) equals the intersection of the numeral of k with val(k) for every k, and some val(k) equals the set of i for which v(i) denotes bottom, then falsehood follows. This is Scott's Theorem 3.4 for an r.e. undefined-index set; the hypothesis that the set of indices denoting bottom is recursively enumerable is not used.

Apply the diagonal contradiction, taking the set of indices to be those whose value is bottom.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_4_diagonal

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 3.4** for an r.e. undefined-index set. -/
theorem theorem_3_4_re_diagonal {val : ℕ → Pomega} {v : ℕ → ℕ}
    (hv : ∀ k, val (v k) = ofNat k ∩ val k)
    (_hRE : IsRE {j | val j = botElem})
    (hex : ∃ k, val k = {i | v i ∈ {j | val j = botElem}}) : False :=
  theorem_3_4_diagonal hv rfl hex

end DomainTheory.DataTypesAsLattices
