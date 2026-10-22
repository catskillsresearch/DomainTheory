module

public import Mathlib.Data.Set.Basic
public import Mathlib.Order.Hom.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.NeighborhoodSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Element
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_zero
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.interUpTo_succ
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst22
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_principal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.mem_bot
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.BasicInst34
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.DomainIso

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- Scott's `𝒟₀ ≅ 𝒟₁`: the domains are isomorphic (there *exists* a `DomainIso`). -/
def Isomorphic {α β : Type*} (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) : Prop :=
  Nonempty (DomainIso V₀ V₁)

end DomainTheory.NeighbourhoodSystems
