/-ai
A token lies in an element if and only if it lies in the closure of some consistent finite set contained in the element.

If the token lies in the element, its singleton is consistent and contained in the element, and reflexivity puts the token in the closure of that singleton. Conversely, deductive closure of the element applies the entailment witnessing membership in such a closure.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- **Factoid 3.6.** Membership in `x` iff membership in some finite approximation `ū ⊆ x`. -/
theorem mem_element_iff_mem_closure (x : sys.Element) (a : α) :
    a ∈ x.carrier ↔ a ∈ sys.approxUnion x := by
  constructor
  · intro ha
    refine ⟨{a}, sys.con_sing a, ?_, ?_⟩
    · intro b hb
      have hb' : b ∈ ({a} : Finset α) := Finset.mem_coe.1 hb
      rw [Finset.mem_singleton] at hb'
      subst hb'
      exact ha
    · exact sys.ent_refl (sys.con_sing a) (Finset.mem_singleton_self a)
  · rintro ⟨u, hu, hsub, ha⟩
    exact x.closed u a hsub ha

end InfoSys
end DomainTheory.InformationSystems
