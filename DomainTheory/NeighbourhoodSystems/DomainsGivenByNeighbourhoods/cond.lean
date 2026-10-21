/-ai
The consistency test at stage n holds when the running intersection through n, met with the next enumerated set, is a neighbourhood. The test is an abbreviation so that decidability of neighbourhood membership is found through it.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.acc

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise123

open NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α) (enum : ℕ → Set α) [DecidablePred V.mem]

/-- The consistency test at stage `n+1`: is `enum (n+1)` consistent with the prefix `Y₀,…,Yₙ`?
An `abbrev` so the `[DecidablePred V.mem]` instance is found through it. -/
abbrev cond (n : ℕ) : Prop := V.mem (acc V enum n ∩ enum (n + 1))

end Exercise123

end DomainTheory.NeighbourhoodSystems
