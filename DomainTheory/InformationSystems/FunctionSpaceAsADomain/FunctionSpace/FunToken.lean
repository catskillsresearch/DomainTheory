module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys.InfoSys

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

universe u v

variable {α : Type u} {β : Type v} [DecidableEq α] [DecidableEq β]

def FunToken (A : InfoSys α) (B : InfoSys β) : Type _ :=
  {p : Finset α × Finset β // p.1 ∈ A.Con ∧ p.2 ∈ B.Con}

end InfoSys

end DomainTheory.InformationSystems
