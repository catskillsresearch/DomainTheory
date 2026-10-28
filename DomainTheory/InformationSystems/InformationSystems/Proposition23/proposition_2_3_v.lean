module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

theorem proposition_2_3_v {u u' v v' : Finset α}
    (hu : u ∈ sys.Con) (hu' : u' ∈ sys.Con)
    (hsubu : u ⊆ u') (huv : sys.EntSet u v) (hsubv : v' ⊆ v) :
    sys.EntSet u' v' := by
  intro X hX
  have hEnt : sys.Ent u X := huv X (hsubv hX)
  refine sys.ent_trans hu' hu ?_ hEnt
  intro y hy
  exact sys.ent_refl hu' (hsubu hy)

end InfoSys
end DomainTheory.InformationSystems
