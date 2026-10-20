module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.V_diff_mem

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem







theorem V_diffClosed : V.DiffClosed := fun hX hY => V_diff_mem hX hY

end DomainTheory.NeighbourhoodSystems
