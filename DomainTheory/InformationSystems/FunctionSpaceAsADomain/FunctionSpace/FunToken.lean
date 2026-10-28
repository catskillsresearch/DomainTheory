
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

def FunToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : Finset α × Finset β // p.1 ∈ A.Con ∧ p.2 ∈ B.Con}

end InfoSys

end DomainTheory.InformationSystems
