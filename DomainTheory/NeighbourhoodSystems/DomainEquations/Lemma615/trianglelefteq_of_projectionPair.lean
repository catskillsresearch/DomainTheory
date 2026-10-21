/-ai
A projection pair from a neighbourhood system D to a neighbourhood system E, with the projection composed after the injection equal to the identity on D and the injection composed after the projection contained in the identity on E, exhibits D as a subdomain of E.

The witness is the prime system built from the two maps, the fact that this prime system is a subsystem, and the equivalence of that prime system with D.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainEquations.Definition610
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Lemma615.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


section ProjectionPair

variable (i : ApproximableMap D E) (j : ApproximableMap E D)


/-- **Lemma 6.15 (Scott 1981, PRG-19).** A projection pair `i : D → E`, `j : E → D` with
`j ∘ i = I_D` and `i ∘ j ⊆ I_E` exhibits `D` as a subdomain of `E`: `D ⊴ E`. This is the converse
of Proposition 6.12 (`Subsystem.projectionPair`). -/
theorem trianglelefteq_of_projectionPair (hji : j.comp i = idMap D)
    (hij : i.comp j ≤ idMap E) : D ⊴ E :=
  ⟨Dprime i j, Dprime_subsystem i j, ⟨dprimeEquiv i j hji hij⟩⟩

end ProjectionPair
end DomainTheory.NeighbourhoodSystems
