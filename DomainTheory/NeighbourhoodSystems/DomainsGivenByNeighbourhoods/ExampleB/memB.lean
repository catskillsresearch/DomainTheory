/-ai
A set of finite binary strings belongs to the binary neighbourhood system when it is the cone of some string.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Str
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.cone
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.mem_cone

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem

/-- Membership in Scott's binary neighbourhood system `B`: `X ∈ B` iff `X = σΣ*` for some `σ`. -/
def memB (X : Set Str) : Prop := ∃ σ, X = cone σ

end DomainTheory.NeighbourhoodSystems.ExampleB
