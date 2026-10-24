module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Cnat
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.Cone
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.MExpr
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise622.NStarExpr

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB

namespace Exercise619


/-- `Λ ∈ tok(Cnat)`, so `Cnat` is a rooted constant. -/
theorem nil_mem_Cnat : ([] : Str) ∈ Cnat.sys.master := Set.mem_insert_iff.mpr (Or.inr rfl)

end Exercise619
end DomainTheory.NeighbourhoodSystems
