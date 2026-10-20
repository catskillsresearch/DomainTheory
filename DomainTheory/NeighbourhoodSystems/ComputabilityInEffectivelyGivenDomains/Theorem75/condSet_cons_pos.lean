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

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- `condSet` cons-step when the input dominates the head entry's input: intersect `A` with the
head's output. -/
theorem condSet_cons_pos {k : ℕ} {A : Set β} {e : ℕ} {el : List ℕ}
    (h : P₀.X k ⊆ P₀.X e.unpair.1) :
    condSet P₀ P₁ k A (e :: el) = condSet P₀ P₁ k (A ∩ P₁.X e.unpair.2) el := by
  ext z
  simp only [mem_condSet, List.mem_cons, Set.mem_inter_iff]
  constructor
  · rintro ⟨hzA, hall⟩
    exact ⟨⟨hzA, hall e (Or.inl rfl) h⟩, fun e' he' hsub => hall e' (Or.inr he') hsub⟩
  · rintro ⟨⟨hzA, hzE⟩, hall⟩
    exact ⟨hzA, fun e' he' hsub => he'.elim (fun heq => heq ▸ hzE) (fun hmem => hall e' hmem hsub)⟩

end DomainTheory.NeighbourhoodSystems
