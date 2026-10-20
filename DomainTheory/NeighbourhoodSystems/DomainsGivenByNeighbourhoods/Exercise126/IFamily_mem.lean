module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem_mem

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

theorem IFamily_mem (F : Finset A) : (ringSystem (A := A)).mem (IFamily F) := ⟨F, rfl⟩

end Ring

end DomainTheory.NeighbourhoodSystems
