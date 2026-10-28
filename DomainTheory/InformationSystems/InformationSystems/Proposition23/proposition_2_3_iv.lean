module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem proposition_2_3_iv {u v w : Finset α}
    (hu : u ∈ sys.Con) (hv : v ∈ sys.Con)
    (huv : sys.EntSet u v) (hvw : sys.EntSet v w) : sys.EntSet u w :=
  fun X hX => sys.ent_trans hu hv huv (hvw X hX)

end InfoSys
end DomainTheory.InformationSystems
