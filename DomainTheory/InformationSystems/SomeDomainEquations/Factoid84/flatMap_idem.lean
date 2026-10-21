/-ai
The flat map is idempotent: its composite with itself equals itself.

Extensionality of approximable maps reduces the claim to equality of relations. If the composite relates a domain set to a codomain set through an intermediate set, either 1 lies in the domain set, which is already the first clause of the flat relation, or the intermediate set excludes 1, so the second relation cannot place 1 there. The remaining clauses then compose, and each token of the codomain set equals 0 or lies in the domain set, while 1 stays out of the codomain set. Conversely, if 1 lies in the domain set, inserting 1 into the codomain set gives an intermediate witness related on both sides by the first clause. Otherwise the codomain set itself is an intermediate witness: the given clause relates the domain set to it, and it is related to itself because every one of its tokens belongs to it and 1 remains excluded.
ai-/
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.flatMap

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open InfoSys

open ApproximableMap

namespace Factoid84

theorem flatMap_idem : IdemApprox flatMap := by
  refine ApproximableMap.ext fun u v => ?_
  constructor
  · rintro ⟨w, hf, hg⟩
    rcases hf with h1u | ⟨hw, hw1⟩
    · exact Or.inl h1u
    · rcases hg with h1w | ⟨hv, hv1⟩
      · exact False.elim (hw1 h1w)
      · refine Or.inr ⟨?_, hv1⟩
        · intro n hn
          have hn' := hv n hn
          rcases hn' with rfl | hn'
          · exact Or.inl rfl
          · exact hw n hn'
  · intro h
    rcases h with h1u | ⟨hv, hv1⟩
    · exact ⟨insert 1 v, Or.inl h1u, Or.inl (Finset.mem_insert_self 1 v)⟩
    · exact ⟨v, Or.inr ⟨hv, hv1⟩, Or.inr ⟨fun n hn => Or.inr hn, hv1⟩⟩

end Factoid84

end DomainTheory.InformationSystems
