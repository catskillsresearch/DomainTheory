
module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.approxUnion

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
