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
