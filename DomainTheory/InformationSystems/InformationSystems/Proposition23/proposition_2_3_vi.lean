module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.InformationSystems.Definition22

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Proposition 2.3(vi).** `u ⊢ v` and `u ⊢ v'` imply `u ⊢ v ∪' v'`. -/
theorem proposition_2_3_vi {u v v' : Finset α}
    (huv : sys.EntSet u v) (huv' : sys.EntSet u v') : sys.EntSet u (v ∪' v') := by
  intro X hX
  rcases mem_funion.mp hX with h | h
  · exact huv X h
  · exact huv' X h

end InfoSys
end DomainTheory.InformationSystems
