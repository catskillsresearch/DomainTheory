/-ai
Applying a concatenated finite binary string to an element agrees with applying the second string and then the first.

Compare elements by membership of a neighbourhood. A witness for the combined application, prepended with the second string, witnesses the inner application, and associativity of prepending transports the inclusion. Conversely, a witness that itself comes from an inner neighbourhood transports the inclusion by monotonicity of prepending and associativity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Data.List.Infix
import all Mathlib.Data.List.Infix
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.prepend_mono
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.ExampleB.prepend_append

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.ExampleB

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem























/-- **`σ` and `τ` prepend in sequence, like concatenation.** `(στ)x = σ(τx)`: applying the
prefix `σ ++ τ` in one step agrees with applying `τ` first and then `σ`. (Used in Exercise 2.16's
second half — the uniqueness of the parity map — to unfold `f(σ₁σ₂ … σₙx)` one token at a time.) -/
theorem sigmaElt_append (σ τ : Str) (x : B.Element) :
    sigmaElt (σ ++ τ) x = sigmaElt σ (sigmaElt τ x) := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨hY, X, hX, hsub⟩
    refine ⟨hY, prepend τ X, ⟨memB_prepend τ (x.sub hX), X, hX, subset_rfl⟩, ?_⟩
    rw [prepend_append]; exact hsub
  · rintro ⟨hY, X, ⟨_, X', hX', hsub'⟩, hsub⟩
    refine ⟨hY, X', hX', ?_⟩
    rw [← prepend_append]
    exact (prepend_mono σ hsub').trans hsub

end DomainTheory.NeighbourhoodSystems.ExampleB
