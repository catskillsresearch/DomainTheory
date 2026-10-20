module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf_valid
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.rel_interYs_funList

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- **Function-space inclusion characterisation (choice-free).** With `ea` consistent (so the least
map exists), `stepFun (funListOf ea) ⊆ stepFun (funListOf eb)` iff for every entry `e' ∈ eb`, the
intersection of the `ea`-outputs relevant to the input `X₀_{e'.1}` is contained in `X₁_{e'.2}`. -/
theorem stepFun_funListOf_subset_iff {ea eb : List ℕ}
    (hcons : ∀ {X : Set α}, V₀.mem X → V₁.mem (interYs V₁.master (funListOf P₀ P₁ ea) X)) :
    (stepFun (funListOf P₀ P₁ ea) : Set (ApproximableMap V₀ V₁)) ⊆ stepFun (funListOf P₀ P₁ eb) ↔
      ∀ e' ∈ eb, interYs V₁.master (funListOf P₀ P₁ ea) (P₀.X e'.unpair.1) ⊆ P₁.X e'.unpair.2 := by
  have hL : ∀ p ∈ funListOf P₀ P₁ ea, V₀.mem p.1 ∧ V₁.mem p.2 := funListOf_valid P₀ P₁ ea
  constructor
  · intro hsub e' he'
    have hmem := hsub (leastMap_mem_stepFun hL hcons)
    have hrel := hmem (funPair P₀ P₁ e') (List.mem_map.mpr ⟨e', he', rfl⟩)
    exact (leastMap_rel.mp hrel).2.2
  · intro hcond f hf p hp
    rw [funListOf, List.mem_map] at hp
    obtain ⟨e', he', rfl⟩ := hp
    show f.rel (P₀.X e'.unpair.1) (P₁.X e'.unpair.2)
    exact f.mono (rel_interYs_funList P₀ P₁ hf e'.unpair.1) subset_rfl (hcond e' he')
      (P₀.mem_X _) (P₁.mem_X _)

end DomainTheory.NeighbourhoodSystems
