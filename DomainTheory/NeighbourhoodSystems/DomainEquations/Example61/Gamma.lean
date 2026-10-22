module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem

namespace Example61

variable {α : Type*}

/-- The master neighbourhood `Γ = {1,2}* 0 Δ` of `D^§`: any path, `D`-token in `Δ`. -/
def Gamma (D : NeighborhoodSystem α) : Set (List Bool × α) := {t | t.2 ∈ D.master}

end Example61
end DomainTheory.NeighbourhoodSystems
