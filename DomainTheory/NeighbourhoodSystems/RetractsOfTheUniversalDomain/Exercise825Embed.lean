/-ai
Every domain is a subdomain of its infinite power. Specialized to the universal domain, this is Scott's embedding of the universal domain into its infinite power.

The numbered name example_825_embed is that statement.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise825Embed.trianglelefteq_iterSys

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

set_option linter.unusedVariables false

theorem example_825_embed.{u_1} : ∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
  @DomainTheory.NeighbourhoodSystems.Trianglelefteq α (Prod Nat α) V (@DomainTheory.NeighbourhoodSystems.iterSys α V) :=
  @DomainTheory.NeighbourhoodSystems.trianglelefteq_iterSys

end DomainTheory.NeighbourhoodSystems
