/-ai
Bottom approximates every element.

A neighbourhood of bottom equals the master neighbourhood, and every element contains the master neighbourhood.
ai-/
module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_bot

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Factoid 1.8a (Scott 1981, PRG-19).** "The element that approximates all others, `{Δ}`,
is called `⊥`": `⊥` is the least element of `|𝒟|`, `⊥ ⊑ x` for every `x`.

Given `Y ∈ ⊥`, i.e. `Y = Δ`, membership `Δ ∈ x` is filter condition (i) (`x.master_mem`). -/
theorem bot_le (x : V.Element) : V.bot ≤ x := by
  intro Y hY
  rw [mem_bot] at hY
  subst hY
  exact x.master_mem

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
