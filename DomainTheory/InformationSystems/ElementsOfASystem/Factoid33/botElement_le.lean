/-ai
The bottom element lies below every element.

A token of the bottom element is entailed by the singleton of the bottom token. That singleton is contained in every element, because every element contains the bottom token, and deductive closure puts the entailed token in the element.
ai-/

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
