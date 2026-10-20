module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.RingTheory.Ideal.Span
import all Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_IFamily
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ringSystem_mem
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.idealOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_idealOf
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.ofIdeal
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise126.mem_ofIdeal_IFamily

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Ring

open NeighborhoodSystem

variable {A : Type*} [CommRing A]

variable [DecidableEq A]

theorem idealOf_ofIdeal (J : Ideal A) : idealOf (ofIdeal J) = J := by
  apply SetLike.ext
  intro a
  rw [mem_idealOf, mem_ofIdeal_IFamily, Finset.coe_singleton, Ideal.span_singleton_le_iff_mem]

end Ring

end DomainTheory.NeighbourhoodSystems
