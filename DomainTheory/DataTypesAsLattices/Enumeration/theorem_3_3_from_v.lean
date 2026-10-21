/-ai
Scott's Theorem 3.3 (iii) follows from (i) and (ii): if val(v(n)) equals the second recursion value of val(n), then val(rec(n)) equals val(n) applied to the numeral of rec(n).

Rewrite rec by its definition, then use the application equation for val, the hypothesis, equation 3.12, and the application equation for the second recursion value. An element of the resulting union is witnessed by an index belonging to the numeral of v(n), hence by that index equal to v(n). Conversely, v(n) itself belongs to that numeral and is a witness.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.secondRecVal_app
public import DomainTheory.DataTypesAsLattices.Enumeration.eq_3_12

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 3.3 (iii)** from (i) and (ii):
`val(rec(n)) = val(n)(rec(n))`. -/
theorem theorem_3_3_from_v (v : ℕ → ℕ) (n : ℕ)
    (hv : valNat (v n) = secondRecVal (valNat n)) :
    valNat (recNat v n) = funOf (valNat n) (ofNat (recNat v n)) := by
  rw [recNat, valNat_apply, hv, eq_3_12, secondRecVal_app]
  ext k
  constructor
  · intro hk
    obtain ⟨m, hm, hkm⟩ := Set.mem_iUnion₂.mp hk
    simp [ofNat] at hm; subst hm; exact hkm
  · intro hk
    exact Set.mem_iUnion₂.mpr ⟨v n, rfl, hk⟩

end DomainTheory.DataTypesAsLattices
