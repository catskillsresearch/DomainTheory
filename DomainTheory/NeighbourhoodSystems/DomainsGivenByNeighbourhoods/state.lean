/-ai
The greedy state at stage 0 pairs the first enumerated set with its intersection against the master neighbourhood. At a successor, if the current running intersection meets the next enumerated set in a neighbourhood, the state becomes that enumerated set paired with the intersection; otherwise the state is left unchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- Greedy *state*: `state n = (Yₙ, ⋂_{i≤n} Yᵢ)`. The running intersection in the second
component lets the consistency test `V.mem (acc ∩ enum (n+1))` be self-contained (Theorem 1.1c:
the prefix `Y₀,…,Yₙ,enum (n+1)` is consistent iff this intersection is a neighbourhood). -/
def state : ℕ → Set α × Set α
  | 0 => (enum 0, V.master ∩ enum 0)
  | (n + 1) =>
      if V.mem ((state n).2 ∩ enum (n + 1)) then
        (enum (n + 1), (state n).2 ∩ enum (n + 1))
      else
        state n

end Exercise123

end DomainTheory.NeighbourhoodSystems
