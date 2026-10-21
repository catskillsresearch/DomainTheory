/-ai
Factoid 4.1 defines the binary meet of two elements to be the element whose carrier is their intersection. A finite subset of the intersection is a finite subset of each element, so it is consistent, and both elements contribute the closure under entailment.
ai-/
module

public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

/-- **Factoid 4.1.** Binary meet of elements is set-theoretic intersection. -/
def inf (x y : sys.Element) : sys.Element where
  carrier := x.carrier ∩ y.carrier
  consistent := fun Y hY =>
    x.consistent Y (Set.Subset.trans hY Set.inter_subset_left)
  closed := fun Y a hY hEnt =>
    ⟨x.closed Y a (Set.Subset.trans hY Set.inter_subset_left) hEnt,
     y.closed Y a (Set.Subset.trans hY Set.inter_subset_right) hEnt⟩

end InfoSys

end DomainTheory.InformationSystems
