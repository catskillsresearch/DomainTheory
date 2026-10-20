module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Proposition612
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812g4
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise817.ProjPair

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Subsystem

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- **Universality, as an abstract predicate**: every countable neighbourhood system embeds
(up to isomorphism) as a subsystem of `W` — Theorem 8.8(a)'s property, extracted from the specific
domain `𝒰` to an arbitrary `W`. -/
def IsUniversal {δ : Type w} (W : NeighborhoodSystem δ) : Prop :=
  ∀ {α : Type u} (D : NeighborhoodSystem α) [Countable {S : Set α // D.mem S}], D ⊴ W

end DomainTheory.NeighbourhoodSystems
