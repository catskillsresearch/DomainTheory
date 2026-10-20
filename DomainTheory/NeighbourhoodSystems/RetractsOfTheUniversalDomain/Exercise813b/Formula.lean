module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise813a

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

/-- A minimal propositional-logic syntax over `ℵ₀` variables (indexed by `ℕ`). -/
inductive Formula : Type
  | var (i : ℕ) : Formula
  | bot : Formula
  | top : Formula
  | neg (φ : Formula) : Formula
  | and (φ ψ : Formula) : Formula
  | or (φ ψ : Formula) : Formula

end DomainTheory.NeighbourhoodSystems
