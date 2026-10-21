/-ai
If the indexed neighbourhood is not contained in the head input, the conditional set of a cons equals the conditional set of the tail.

Compare membership. The head obligation is impossible under the failed inclusion, so it drops out of the quantifier over the cons.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.condSet
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.mem_condSet

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- `condSet` cons-step when the input does not dominate the head entry's input: drop the head. -/
theorem condSet_cons_neg {k : ℕ} {A : Set β} {e : ℕ} {el : List ℕ}
    (h : ¬ P₀.X k ⊆ P₀.X e.unpair.1) :
    condSet P₀ P₁ k A (e :: el) = condSet P₀ P₁ k A el := by
  ext z
  simp only [mem_condSet, List.mem_cons]
  constructor
  · rintro ⟨hzA, hall⟩
    exact ⟨hzA, fun e' he' hsub => hall e' (Or.inr he') hsub⟩
  · rintro ⟨hzA, hall⟩
    exact ⟨hzA, fun e' he' hsub => he'.elim (fun heq => absurd (heq ▸ hsub) h) (fun hmem => hall e' hmem hsub)⟩

end DomainTheory.NeighbourhoodSystems
