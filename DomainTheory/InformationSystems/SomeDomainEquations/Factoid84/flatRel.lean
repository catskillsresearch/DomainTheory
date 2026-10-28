module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid34
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid84.IsDomainApprox

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive
open InfoSys
open ApproximableMap

namespace Factoid84

def flatRel (u v : Finset ℕ) : Prop :=
  (1 ∈ u) ∨ ((∀ n ∈ v, n = 0 ∨ n ∈ u) ∧ 1 ∉ v)

theorem flatRel.empty : flatRel ∅ ∅ :=
  Or.inr ⟨fun _ hn => False.elim (Finset.notMem_empty _ hn), Finset.notMem_empty _⟩

theorem flatRel.of_mem_one {u v : Finset ℕ} (h : 1 ∈ u) : flatRel u v :=
  Or.inl h

end Factoid84

end DomainTheory.InformationSystems
