module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)




theorem subset_deductiveClosure (U : Set α) (hU : sys.IsFinitelyConsistent U) :
    U ⊆ (sys.deductiveClosure U hU).carrier := by
  intro a ha
  refine ⟨{a}, ?_, sys.ent_refl (hU {a} ?_) (Finset.mem_singleton_self a)⟩
  · intro b hb
    have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact ha
  · intro b hb
    have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact ha

end InfoSys
end DomainTheory.InformationSystems
