/-ai
A token of the function space from A to B, in the sense of Scott's Definition 7.1(i), is a pair of a finite set of A and a finite set of B, both required to be consistent.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

/-- Token type of the function space `A → B` (Scott 7.1(i)). -/
def FunToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : Finset α × Finset β // p.1 ∈ A.Con ∧ p.2 ∈ B.Con}

end InfoSys

end DomainTheory.InformationSystems
