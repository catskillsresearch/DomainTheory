/-ai
A ternary relation is recursively decidable when a primitive-recursive function of the nested pairing code returns only zero or one and returns one exactly on the triples in the relation.

Ternary decidability is unary decidability of the nested pairing, and the unary zero-one bridge applies. The specification rewrites by the pairing round-trip applied twice.
ai-/
module

public import Mathlib.Data.Nat.Sqrt
import all Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
import all Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
import all Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
import all Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
import all Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
import all Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.RecDecidableu2eof_zero_one_char

@[expose] public section


namespace Domain.Recursive











































/-- **Triple `{0,1}` characteristic.** When the Bool decider has been packaged as a unary
primitive-recursive function on `Nat.pair n (Nat.pair m k)`, reindex to `RecDecidable₃`. -/
theorem RecDecidable₃.of_triple_zero_one_char {r : ℕ → ℕ → ℕ → Prop} {f : ℕ → ℕ}
    (hf : Nat.Primrec f) (h01 : ∀ t, f t = 0 ∨ f t = 1)
    (hfe : ∀ n m k, r n m k ↔ f (Nat.pair n (Nat.pair m k)) = 1) :
    RecDecidable₃ r := by
  unfold RecDecidable₃
  refine RecDecidable.of_zero_one_char hf h01 (fun t => ?_)
  rw [hfe, pair_unpair, pair_unpair]

end Domain.Recursive
