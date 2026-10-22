module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Proposition23

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Scott 6.1(i): a product token is `(X, Δ_B)` or `(Δ_A, Y)`. -/
class IsProdToken (A : InfoSys α) (B : InfoSys β) (p : α × β) : Prop where
  out : p.1 = A.bot ∨ p.2 = B.bot

end InfoSys

end DomainTheory.InformationSystems
