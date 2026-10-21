/-ai
If the consistency character is primitive recursive, then the relation asserting that some enumerated set is contained in the intersection of two enumerated sets is recursively decidable.

The paired zero-one character theorem applies to that primitive recursion, the fact that the character takes values in {0, 1}, and the equivalence of the character equaling 1 with the consistency relation.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ConsistencyPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.SsysX
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722PresentationInst47
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssysConsChar_zero_one
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.ssys_cons_char_eq_one_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace Exercise722

open Set Domain.Recursive

set_option maxHeartbeats 5000000

/-- **Conditional C9 closure.** Instantiated once the sole missing primitive-recursive link below
is proved. -/
theorem Ssys_cons_computable_of_primrec_ssysConsChar (hf : Nat.Primrec ssysConsChar) :
    RecDecidable₂ (fun n m => ∃ k, SsysX k ⊆ SsysX n ∩ SsysX m) :=
  RecDecidable₂.of_paired_zero_one_char hf ssysConsChar_zero_one ssys_cons_char_eq_one_iff

end Exercise722

end DomainTheory.NeighbourhoodSystems
