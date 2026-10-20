module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.appendCode
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.decodeList_appendCode

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- `stepFun (funListOf (decodeList (appendCode a b)))` is exactly `X a ∩ X b` at the level of the
underlying step-intersections. -/
theorem stepFun_funListOf_appendCode (a b : ℕ) :
    (stepFun (funListOf P₀ P₁ (decodeList (appendCode a b))) : Set (ApproximableMap V₀ V₁)) =
      stepFun (funListOf P₀ P₁ (decodeList a)) ∩ stepFun (funListOf P₀ P₁ (decodeList b)) := by
  ext f
  rw [decodeList_appendCode]
  simp only [funListOf, List.map_append, List.map_reverse, mem_stepFun, Set.mem_inter_iff,
    List.mem_append, List.mem_reverse]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inr hp), fun p hp => h p (Or.inl hp)⟩
  · rintro ⟨ha, hb⟩ p (hp | hp)
    · exact hb p hp
    · exact ha p hp

end DomainTheory.NeighbourhoodSystems
