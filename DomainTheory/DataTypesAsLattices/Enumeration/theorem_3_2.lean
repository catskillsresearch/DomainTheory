/-ai
Scott's enumeration theorem (Theorem 3.2) asserts that the recursively enumerable elements are the values val(n) for n a natural number, with val(0) = G and val(apply(n)(m)) = val(n) applied to val(m). Formally, every val(n) is recursively enumerable, val(0) equals G, and the value of an application code is the application of the values.

The three clauses are the combinatory character of every value, the zero equation for val, and the application equation for val.
ai-/

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
