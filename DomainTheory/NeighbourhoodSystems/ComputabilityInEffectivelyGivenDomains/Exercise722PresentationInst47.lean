module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsistentB
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_char_iff

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

/-- Scott's consistency relation (Definition 7.1 (ii)) on the `SsysX` indices is decidable via
`ssysConsistentB` (choice-free on the `Bool` side; see axiom audit of `decideNonemptyB_iff`). -/
instance decidableSsysCons (n m : ℕ) :
    Decidable (∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  decidable_of_iff (ssysConsistentB n m = true) (ssys_cons_char_iff n m)

end Exercise722

end DomainTheory.NeighbourhoodSystems
