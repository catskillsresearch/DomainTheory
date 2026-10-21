/-ai
Every finite list of step pairs of neighbourhoods is the step list of some entry list.

The empty list is the empty entry list. For a cons, choose indices of the two components of the head and an entry list for the tail, and cons the paired index. The cons equation for the step list and the pair projections match the head.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition72
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.interList_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_fst
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funPair_snd
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.bitSelect_nil
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75.funListOf_cons

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- Every valid finite step-list is `funListOf` of some entry-list (choice-free: `Exists.elim` of
`P₀.surj`/`P₁.surj`, entry by entry). -/
theorem exists_funListOf {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    ∃ el, funListOf P₀ P₁ el = L := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons p L ih =>
    obtain ⟨X, Y⟩ := p
    obtain ⟨i, hi⟩ := P₀.surj (hL (X, Y) (List.mem_cons.mpr (Or.inl rfl))).1
    obtain ⟨j, hj⟩ := P₁.surj (hL (X, Y) (List.mem_cons.mpr (Or.inl rfl))).2
    obtain ⟨el, hel⟩ := ih (fun q hq => hL q (List.mem_cons.mpr (Or.inr hq)))
    refine ⟨Nat.pair i j :: el, ?_⟩
    rw [funListOf_cons, hel]
    congr 1
    show (P₀.X (Nat.pair i j).unpair.1, P₁.X (Nat.pair i j).unpair.2) = (X, Y)
    rw [unpair_pair_fst, unpair_pair_snd, hi, hj]

end DomainTheory.NeighbourhoodSystems
