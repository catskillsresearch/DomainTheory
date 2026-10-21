/-ai
The subset characteristic of a paired code is the prefix characteristic of the second component against the first. It is the zero-one test of inclusion of the neighbourhood enumerated by the first component in the neighbourhood enumerated by the second, packaged as a named unary function.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.LFunData
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.BasicInst2
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inl
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.cons_inr
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_mem
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise724.L_master

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise724

open NeighborhoodSystem Domain.Recursive

/-- **`Xₙ ⊆ Xₘ` `{0,1}` characteristic**, packaged as a single *named* unary function (rather than
an anonymous `t.unpair`-lambda passed positionally to `RecDecidable₂.of_paired_zero_one_char`):
naming it lets the `hfe` obligation be stated and proved as a standalone lemma whose conclusion is
syntactically `LenumSubsetChar (Nat.pair n m) = 1`, so the final application only needs to match
this name against itself — no elaborator-side defeq unfolding of `Nat.pair`/`Nat.unpair` (which is
expensive and blows the `whnf` budget; see the project's course-of-values discipline). -/
def LenumSubsetChar (t : ℕ) : ℕ := isPrefixChar t.unpair.2 t.unpair.1

end DomainTheory.NeighbourhoodSystems.Exercise724
