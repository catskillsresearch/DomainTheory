/-ai
Prepending one finite binary string and then another agrees with prepending their concatenation.

Compare the two sets by extensionality. A string in the iterated prepend is the first string concatenated with a concatenation of the second string with a member of the set, and associativity reassociates it. Conversely, a concatenation of the combined string with a member splits as the first string followed by the second string concatenated with that member.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem


/-- **Prepending is associative.** `σ(τX) = (στ)X`: prepending `σ` after `τ` is the same as
prepending the concatenation `σ ++ τ` in one step (used to compose `sigmaElt`, `Exercise216`). -/
theorem prepend_append (σ τ : Str) (X : Set Str) :
    prepend σ (prepend τ X) = prepend (σ ++ τ) X := by
  ext w
  simp only [mem_prepend]
  constructor
  · rintro ⟨ρ, ⟨ρ', hρ', rfl⟩, rfl⟩
    exact ⟨ρ', hρ', by rw [List.append_assoc]⟩
  · rintro ⟨ρ, hρ, rfl⟩
    exact ⟨τ ++ ρ, ⟨ρ, hρ, rfl⟩, by rw [List.append_assoc]⟩

end DomainTheory.NeighbourhoodSystems.ExampleB
