/-ai
The map from the Lindenbaum algebra to sets of natural numbers is injective.

Induct on both quotient classes, reducing to formulas. Equality of their images is semantic equivalence, by the agreement of semantic equivalence with equality of evaluation sets, and the quotient relation identifies the classes.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


















/-- **`Lindenbaum.toSet` is injective.** -/
theorem Lindenbaum.toSet_injective : Function.Injective Lindenbaum.toSet := by
  intro x y
  induction x using Quotient.ind with
  | _ φ =>
    induction y using Quotient.ind with
    | _ ψ =>
      intro h
      exact Quotient.sound (semanticEquiv_iff_evalSet_eq.mpr h)

end DomainTheory.NeighbourhoodSystems
