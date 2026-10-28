module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Pomega.e

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

class Extensional (val : ℕ → Pomega) (p : ℕ → ℕ) : Prop where
  out : ∀ n m, val n = val m → val (p n) = val (p m)

end DomainTheory.DataTypesAsLattices
