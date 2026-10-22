
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_combinatory

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- **Scott 1976, Theorem 3.2 (The enumeration theorem).**
`RE = {val n | n ∈ ω}`, with `val(0) = G` and
`val(apply(n)(m)) = val n (val m)`. -/
theorem theorem_3_2 :
    (∀ n, valNat n ∈ RE) ∧
      valNat 0 = Gcomb ∧
        (∀ n m, valNat (applyNat n m) = valNat n ⬝ valNat m) :=
  ⟨fun n => valNat_combinatory n, valNat_zero, valNat_apply⟩

end DomainTheory.DataTypesAsLattices
