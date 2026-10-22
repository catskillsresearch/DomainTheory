module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise619PartB
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.GExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621.oplusTok_nonempty

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619

open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619

variable {D₀ D₁ : NeighborhoodSystem Str}

variable {h₀ : ∀ X, D₀.mem X → X.Nonempty} {h₁ : ∀ Y, D₁.mem Y → Y.Nonempty}

/-- The **coalesced sum object** `𝒟₀ ⊕ 𝒟₁`. -/
def ScottSys.oplus (A₀ A₁ : ScottSys) : ScottSys :=
  ⟨oplusTok A₀.sys A₁.sys A₀.ne A₁.ne, oplusTok_nonempty⟩

end Exercise619

end DomainTheory.NeighbourhoodSystems
