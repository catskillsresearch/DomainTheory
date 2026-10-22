module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition613
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Setup
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.mem_colim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_master
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.colim_sub_Tcolim
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem614.Tcolim_sub_colim

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise510

universe w

namespace Theorem614

variable {α : Type w}

/-- **`T(𝒟) = 𝒟`** (Scott's `𝒟 = T(𝒟)`): the two systems have the same neighbourhoods (mutual
inclusion via `colim_sub_Tcolim`/`Tcolim_sub_colim`) and the same master. -/
theorem Tcolim_eq_colim (s : Setup.{w}) : Tcolim s = colim s :=
  NeighborhoodSystem.ext
    (fun _ => ⟨fun h => Tcolim_sub_colim s h, fun h => colim_sub_Tcolim s h⟩)
    (by rw [Tcolim_master, colim_master])

end Theorem614

end DomainTheory.NeighbourhoodSystems
