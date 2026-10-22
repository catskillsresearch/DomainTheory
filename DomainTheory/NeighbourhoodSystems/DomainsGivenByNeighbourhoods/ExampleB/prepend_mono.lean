module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Prepending is monotone.** `X' ⊆ X → σX' ⊆ σX` (Exercise 2.16's `sigmaMap` uses this for
its `mono` clause; `sigmaElt_append` uses it to transport the up-closure through composition). -/
theorem prepend_mono (σ : Str) {X X' : Set Str} (h : X' ⊆ X) : prepend σ X' ⊆ prepend σ X := by
  rintro w ⟨τ, hτ, rfl⟩
  exact ⟨τ, h hτ, rfl⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
