/-ai
The bottom element is a left zero for the meet: its meet with any element is the bottom element.

The criterion that the order is equality with a meet applies to the inequality of the bottom element below the given element.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.Basic
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid41.le_iff_inf_eq

@[expose] public section


namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)


/-- `⊥` is a zero for meet: `⊥ ∩ x = ⊥`. -/
theorem botElement_inf (x : sys.Element) : sys.inf sys.botElement x = sys.botElement :=
  (sys.le_iff_inf_eq (x := sys.botElement) (y := x)).1 (sys.botElement_le x)

end InfoSys
end DomainTheory.InformationSystems
