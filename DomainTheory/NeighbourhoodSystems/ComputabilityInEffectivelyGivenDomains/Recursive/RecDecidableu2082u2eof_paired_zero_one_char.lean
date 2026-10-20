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











































/-- **Paired `{0,1}` characteristic.** When the Bool decider has been packaged as a unary
primitive-recursive function on `Nat.pair n m`, reindex to `RecDecidable₂`. -/
theorem RecDecidable₂.of_paired_zero_one_char {r : ℕ → ℕ → Prop} {f : ℕ → ℕ} (hf : Nat.Primrec f)
    (h01 : ∀ t, f t = 0 ∨ f t = 1) (hfe : ∀ n m, r n m ↔ f (Nat.pair n m) = 1) :
    RecDecidable₂ r := by
  unfold RecDecidable₂
  refine RecDecidable.of_zero_one_char hf h01 (fun t => ?_)
  rw [hfe, pair_unpair]

end Domain.Recursive
