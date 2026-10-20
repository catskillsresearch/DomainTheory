module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise621
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Exercise623.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap DomainTheory.NeighbourhoodSystems.Exercise619
open DomainTheory.NeighbourhoodSystems.Example62 DomainTheory.NeighbourhoodSystems.ExampleB DomainTheory.NeighbourhoodSystems.Exercise510

namespace Exercise619





















































/-- The projection `j : E → D` of a subsystem is **strict**. -/
theorem Subsystem.proj_isStrict {α : Type*} {D E : NeighborhoodSystem α} (h : D ◁ E) :
    IsStrict h.proj := by
  intro X hrel
  rw [Subsystem.proj_rel] at hrel
  obtain ⟨_, hXD, hsub⟩ := hrel
  exact Set.Subset.antisymm (D.sub_master hXD) (by rw [h.master_eq]; exact hsub)

end Exercise619
end DomainTheory.NeighbourhoodSystems
