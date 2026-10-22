module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

@[simp] theorem ringSystem_mem {S : Set (Finset A)} :
    (ringSystem (A := A)).mem S ↔ ∃ F, S = IFamily F := Iff.rfl

end Ring

end DomainTheory.NeighbourhoodSystems
