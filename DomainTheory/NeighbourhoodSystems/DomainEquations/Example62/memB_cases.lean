/-ai
Every neighbourhood of the binary-sequence domain is the master, the false-bit tagging of a neighbourhood, or the true-bit tagging of a neighbourhood.

A neighbourhood is the cone of a finite binary string. The cone of the empty string is the master. A string beginning with false has cone equal to the false-bit tagging of the cone of its tail, and a string beginning with true has cone equal to the true-bit tagging of the cone of its tail.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise319Sum
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.mem_embBit
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Example62.embBit_cone

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap ExampleB

namespace Example62

/-- **Example 6.2 — the shape of a `B`-neighbourhood.** Every neighbourhood of `B` is either the
master `Σ* = cone []`, a `0`-copy `0X` with `X ∈ B`, or a `1`-copy `1X` with `X ∈ B`. -/
theorem memB_cases {W : Set Str} (hW : B.mem W) :
    W = Set.univ ∨ (∃ X, B.mem X ∧ W = embBit false X) ∨ (∃ Y, B.mem Y ∧ W = embBit true Y) := by
  obtain ⟨σ, rfl⟩ := hW
  cases σ with
  | nil => exact Or.inl cone_nil
  | cons b σ' =>
    cases b with
    | false => exact Or.inr (Or.inl ⟨cone σ', memB_cone σ', (embBit_cone false σ').symm⟩)
    | true => exact Or.inr (Or.inr ⟨cone σ', memB_cone σ', (embBit_cone true σ').symm⟩)

end Example62

end DomainTheory.NeighbourhoodSystems
