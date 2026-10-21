/-ai
The prefix characteristic of two list codes is the list-equality characteristic of the first code against the code of the initial segment, of length given by the length characteristic of the first code, of the list coded by the second. The value 1 records that the list coded by the first is a prefix of the list coded by the second.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_zero
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.streamCons_succ
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_consSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.consSet_empty
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.nbhd_cons
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.mem_nbhd

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **The `{0,1}` prefix test.** `isPrefixChar m n = 1 ↔ decodeList m <+: decodeList n`, built from
`Recursive.lean`'s `listLenChar`/`takeCode`/`listEqChar` (already primitive recursive): `l₁ <+: l₂`
iff `l₂.take l₁.length = l₁` (`List.prefix_iff_eq_take`), unconditionally (`List.take` auto-caps at
the available length, so no separate length guard is needed). -/
def isPrefixChar (m n : ℕ) : ℕ := listEqChar (takeCode (listLenChar m) n) m

end DomainTheory.NeighbourhoodSystems.Exercise724
