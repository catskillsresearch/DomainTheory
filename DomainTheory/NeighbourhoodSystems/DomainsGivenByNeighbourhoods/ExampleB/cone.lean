/-ai
The cone of a finite binary string is the set of all strings of which it is a prefix.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
import all Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Str

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- The neighbourhood `σΣ*`: all *extensions* of `σ` (sequences with `σ` as an initial segment). -/
def cone (σ : Str) : Set Str := {w | σ <+: w}

end DomainTheory.NeighbourhoodSystems.ExampleB
