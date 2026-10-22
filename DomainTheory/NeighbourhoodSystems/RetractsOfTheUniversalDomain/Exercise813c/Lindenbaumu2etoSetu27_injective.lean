module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Clopen
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813c.Basic

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Lindenbaumu2erange_toSet
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813b.Lindenbaumu2etoSet_injective
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems


theorem Lindenbaum.toSet'_injective : Function.Injective Lindenbaum.toSet' := by
  intro x y
  induction x using Quotient.ind with
  | _ φ =>
    induction y using Quotient.ind with
    | _ ψ =>
      intro h
      exact Quotient.sound (semanticEquiv_iff_evalSet'_eq.mpr h)

end DomainTheory.NeighbourhoodSystems
