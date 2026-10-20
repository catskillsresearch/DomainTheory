module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Tactic
import all Mathlib.Tactic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Exercise115.flat_no_three_chain

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise115

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem








/-- **Flat has no infinite ascending chain.** -/
theorem flat_no_infinite_chain : ¬ ∃ f : ℕ → flat.Element, StrictMono f := by
  rintro ⟨f, hf⟩
  exact flat_no_three_chain
    ⟨f 0, f 1, f 2, hf (by norm_num), hf (by norm_num)⟩

end DomainTheory.NeighbourhoodSystems.Exercise115
