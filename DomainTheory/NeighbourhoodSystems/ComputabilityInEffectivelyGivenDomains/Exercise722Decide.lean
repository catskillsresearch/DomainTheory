/-ai
This file gathers and re-exports the decision layer for fragment expressions: the consistency bit and nonempty intersection of denotations, the comparison of the number of automaton states with the cardinality of the state type, nonemptiness of an accepted language, emptiness of a denotation, the last state along a path, the short-word criterion for nonemptiness, and the agreement of the consistency bit with the neighbourhood system.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.autStateCard_le_card
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.nfa_accepts_nonempty_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.denote_eq_empty_iff
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.pathStateAt_last
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.nfa_accepts_nonempty_iff_short
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide.consistentB_iff_Ssys

@[expose] public section
