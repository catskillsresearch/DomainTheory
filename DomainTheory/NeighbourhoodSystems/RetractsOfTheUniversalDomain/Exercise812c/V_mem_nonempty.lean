module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem







theorem V_mem_nonempty {X : Set ℕ} (hX : V.mem X) : X.Nonempty := by
  obtain ⟨k, m, -, hne⟩ := hX; exact hne

end DomainTheory.NeighbourhoodSystems
