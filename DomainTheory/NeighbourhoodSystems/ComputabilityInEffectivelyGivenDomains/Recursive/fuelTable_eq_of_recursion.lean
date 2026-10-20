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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.fuelTable_zero_nth
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.fuelTable_succ_nth

@[expose] public section


namespace Domain.Recursive













































































































































































/-- **Course-of-values correctness.** If `bodyLookup` faithfully implements `Body` via table
lookup (`hlookup`), and `Body`'s result at `c` only depends on `prev` restricted to `[0, c]`
(`hlocal` — true whenever `Body`'s own recursive calls are all `≤ c`, e.g. via `Nat.unpair`
projections), then `fuelTable` correctly tabulates the `0`/`Body` fuel recursion on `[0, bound]`. -/
theorem fuelTable_eq_of_recursion {F : ℕ → ℕ → ℕ} {Body : (ℕ → ℕ) → ℕ → ℕ} {bodyLookup : ℕ → ℕ}
    (hF0 : ∀ c, F 0 c = 0) (hFsucc : ∀ fuel c, F (fuel + 1) c = Body (F fuel) c)
    (hlookup : ∀ table c, bodyLookup (Nat.pair table c) = Body (fun c' => nthCode table c' 0) c)
    (hlocal : ∀ (f g : ℕ → ℕ) c, (∀ c' ≤ c, f c' = g c') → Body f c = Body g c) :
    ∀ fuel bound c, c ≤ bound → nthCode (fuelTable bodyLookup bound fuel) c 0 = F fuel c := by
  intro fuel
  induction fuel with
  | zero => intro bound c hc; rw [fuelTable_zero_nth hc, hF0]
  | succ fuel ih =>
    intro bound c hc
    rw [fuelTable_succ_nth hc, hlookup, hFsucc]
    exact hlocal _ _ c fun c' hc' => ih bound c' (le_trans hc' hc)

end Domain.Recursive
