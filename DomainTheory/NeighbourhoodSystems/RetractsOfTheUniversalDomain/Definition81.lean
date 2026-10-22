/-ai
A retraction of a neighbourhood system is an approximable self-map equal to its composite with itself, and the identity map is a retraction.

The identity composite law, applied to the identity map, gives that equality.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Retraction

@[expose] public section

/-!
# Lecture VIII — Definition 8.1 (Scott 1981, PRG-19): retractions

Lecture VIII embeds every domain of interest into one "largest" domain, the universal domain `𝒰`
of Definition 8.7. Before constructing `𝒰` itself, Scott studies how a subdomain `D ◁ E`
corresponds to a self-map of `E` — a *retraction*. As Scott remarks, this analysis lets every
domain-theoretic construction be re-expressed as a `λ`-calculus combinator (culminating in the
`sub` combinator of Theorem 8.6).

**Definition 8.1.** A *retraction* of a domain `E` is an approximable mapping `a : E → E` such that
`a ∘ a = a`.

This module states the definition and the handful of elementary closure facts (`idMap` is always a
retraction; retractions are closed under nothing further at this level of generality — the
interesting closure facts come from Proposition 8.2 onward).

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {E : NeighborhoodSystem α}


/-- The identity mapping `I_E` is (trivially) a retraction. -/
@[simp] theorem isRetraction_idMap : Retraction (idMap E) :=
  ⟨idMap_comp (idMap E)⟩

end DomainTheory.NeighbourhoodSystems
