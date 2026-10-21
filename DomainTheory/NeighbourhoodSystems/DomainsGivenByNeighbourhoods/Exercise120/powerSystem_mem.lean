/-ai
A set of neighbourhoods is a neighbourhood of the power system if and only if it is the up-set of some neighbourhood.

The two sides are the defining condition of the power system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.mem_upSet
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise120.powerSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

@[simp] theorem powerSystem_mem {S : Set (Set α)} :
    V.powerSystem.mem S ↔ ∃ X, V.mem X ∧ S = V.upSet X := Iff.rfl

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
