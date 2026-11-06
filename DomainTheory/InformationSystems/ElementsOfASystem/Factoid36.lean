module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.element_eq_approxUnion
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.mem_element_iff_mem_closure

@[expose] public section

namespace DomainTheory.InformationSystems.InfoSys

theorem theorem_36 :
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x : sys.Element),
      x.carrier = sys.approxUnion x) ∧
    (∀ {α : Type*} [DecidableEq α] (sys : InfoSys α) (x : sys.Element) (a : α),
      a ∈ x.carrier ↔ a ∈ sys.approxUnion x) :=
  ⟨@element_eq_approxUnion, @mem_element_iff_mem_closure⟩

end DomainTheory.InformationSystems.InfoSys
