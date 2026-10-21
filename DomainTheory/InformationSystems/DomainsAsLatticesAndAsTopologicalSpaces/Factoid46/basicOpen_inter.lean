/-ai
The intersection of the basic opens of two finite token sets is the basic open of their union.

An element contains the union exactly when it contains each summand, because every token of the union lies in one summand and each summand is included in the union.
ai-/

module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]


/-- Intersection of basic opens: `[u] ∩ [v] = [u ∪' v]`. -/
theorem basicOpen_inter (A : InfoSys α) (u v : Finset α) :
    A.basicOpen u ∩ A.basicOpen v = A.basicOpen (u ∪' v) := by
  ext x
  constructor
  · intro ⟨hu, hv⟩ a ha
    rcases mem_funion.mp (Finset.mem_coe.1 ha) with h | h
    · exact hu (Finset.mem_coe.2 h)
    · exact hv (Finset.mem_coe.2 h)
  · intro huv
    refine ⟨?_, ?_⟩
    · intro a ha
      exact huv (Finset.mem_coe.2 (mem_funion.mpr (Or.inl (Finset.mem_coe.1 ha))))
    · intro a ha
      exact huv (Finset.mem_coe.2 (mem_funion.mpr (Or.inr (Finset.mem_coe.1 ha))))

end InfoSys
end DomainTheory.InformationSystems
