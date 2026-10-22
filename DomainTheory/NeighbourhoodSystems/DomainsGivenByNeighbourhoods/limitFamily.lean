module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst22

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- The **limit family** of a sequence of neighbourhoods (Scott, the prose before Definition
1.6): `x = {Z ∈ 𝒟 ∣ Xₙ ⊆ Z for some n}` — the family of all neighbourhoods eventually reached
by `⟨Xₙ⟩`. This is the construction Scott uses to motivate the (ideal) elements of `|𝒟|`. -/
def limitFamily (X : ℕ → Set α) : Set (Set α) := {Z | V.mem Z ∧ ∃ n, X n ⊆ Z}

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
