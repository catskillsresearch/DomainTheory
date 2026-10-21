/-ai
The carrier of an element equals the union of the closures of the consistent finite sets contained in it.

Extensionality reduces the equality to the membership form of this identity.
ai-/

module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.Basic
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid36.mem_element_iff_mem_closure

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- **Factoid 3.6.** Carrier form: `x = ⋃{ū | u ∈ Con, u ⊆ x}`. -/
theorem element_eq_approxUnion (x : sys.Element) : x.carrier = sys.approxUnion x := by
  ext a
  exact sys.mem_element_iff_mem_closure x a

end InfoSys
end DomainTheory.InformationSystems
