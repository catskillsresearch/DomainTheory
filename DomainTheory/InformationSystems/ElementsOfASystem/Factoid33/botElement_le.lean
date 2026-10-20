module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid32
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- `⊥` is least. -/
theorem botElement_le (x : sys.Element) : sys.botElement ≤ x := by
  intro a ha
  have hsub : (↑({sys.bot} : Finset α) : Set α) ⊆ x.carrier := by
    intro b hb
    have hb' : b ∈ ({sys.bot} : Finset α) := Finset.mem_coe.1 hb
    rw [Finset.mem_singleton] at hb'
    subst hb'
    exact factoid_3_2 sys x
  exact x.closed {sys.bot} a hsub ha

end InfoSys
end DomainTheory.InformationSystems
