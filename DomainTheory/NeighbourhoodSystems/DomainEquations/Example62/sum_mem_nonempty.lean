module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.B_nonempty
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.BB

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

theorem sum_mem_nonempty {W : Set (Option (Str ⊕ Str))} (h : BB.mem W) : W.Nonempty := by
  rcases h with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩
  · exact ⟨none, none_mem_sumMaster⟩
  · exact inj₀_nonempty (B_nonempty X hX)
  · exact inj₁_nonempty (B_nonempty Y hY)

end Example62

end DomainTheory.NeighbourhoodSystems
