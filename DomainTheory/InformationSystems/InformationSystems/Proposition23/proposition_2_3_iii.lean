module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22
public import DomainTheory.InformationSystems.InformationSystems.Proposition23.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Proposition 2.3(iii).** `u ⊢ u`. -/
theorem proposition_2_3_iii {u : Finset α} (hu : u ∈ sys.Con) : sys.EntSet u u :=
  fun _X hX => sys.ent_refl hu hX

end InfoSys
end DomainTheory.InformationSystems
