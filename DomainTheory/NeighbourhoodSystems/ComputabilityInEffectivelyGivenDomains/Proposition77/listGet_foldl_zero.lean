/-ai
Folding the indexing step from a countdown of zero returns the carried value unchanged.

On the empty list the fold is the start state. On a cons, the step sees countdown zero, so the selection keeps the value, and the inductive hypothesis applies.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example61
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition77.listGetStp_pair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive Example61

variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (P : ComputablePresentation D)

/-- With `cd = 0` the fold is a fixed point on the value. -/
theorem listGet_foldl_zero (l : List ℕ) (val : ℕ) :
    (List.foldl (fun acc x => listGetStp (Nat.pair x (Nat.pair acc 0))) (Nat.pair 0 val) l).unpair.2
      = val := by
  induction l generalizing val with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, listGetStp_pair, Nat.zero_sub,
        show isOne 0 = 0 from rfl, selectFn_zero, ih]

end Proposition77

end DomainTheory.NeighbourhoodSystems
