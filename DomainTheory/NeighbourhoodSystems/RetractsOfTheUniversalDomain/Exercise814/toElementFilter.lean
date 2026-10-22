/-ai
The forward map sends a fixed point to the element of the reconstructed domain whose neighbourhoods are the principal up-sets of compact fixed points lying below it. A confirmed up-set is a neighbourhood of the system by its compact generator. The master neighbourhood is the up-set of the bottom compact, which lies below every fixed point. The intersection of two confirmed up-sets is the up-set of their join, which still lies below the fixed point. An upper neighbourhood of a confirmed up-set is the up-set of a larger compact, and that compact lies below the fixed point because the original compact belongs to the upper up-set.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise127
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.botFix_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.CompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.botK
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.joinCompactFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.joinCompactFix_le
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.self_mem_upFix
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.upFix_inter
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.domainOfClosure
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.ClosureOperator

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : ClosureOperator a)

/-- **The forward map `Fix(a) → |domainOfClosure h|`**: `y ↦ {S ∣ S = ↑k ∧ k ⊑ y}`. -/
def toElementFilter (y : FixSet a) : (domainOfClosure h).Element where
  mem S := ∃ k : CompactFix h, S = upFix h k ∧ k.1.1 ≤ y.1
  sub := fun ⟨k, hSeq, _⟩ => ⟨k, hSeq⟩
  master_mem := ⟨botK h, rfl, botFix_le h y⟩
  inter_mem := by
    rintro S1 S2 ⟨k1, rfl, hk1y⟩ ⟨k2, rfl, hk2y⟩
    exact ⟨joinCompactFix h hk1y hk2y, upFix_inter h k1 k2 hk1y hk2y, joinCompactFix_le h hk1y hk2y⟩
  up_mem := by
    rintro S1 S2 ⟨k1, rfl, hk1y⟩ hS2mem hsub
    obtain ⟨k2, rfl⟩ := hS2mem
    exact ⟨k2, rfl, (mem_upFix h |>.mp (hsub (self_mem_upFix h k1))).trans hk1y⟩

end FiniteDomain

end DomainTheory.NeighbourhoodSystems
