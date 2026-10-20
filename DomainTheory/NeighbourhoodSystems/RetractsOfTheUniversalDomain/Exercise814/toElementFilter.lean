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
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise814.IsClosureOperator

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

universe u

variable {α : Type u} {E : NeighborhoodSystem α}

section FiniteDomain

variable {a : ApproximableMap E E} (h : IsClosureOperator a)

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
