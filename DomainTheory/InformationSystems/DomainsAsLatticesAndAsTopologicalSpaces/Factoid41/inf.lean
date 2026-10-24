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

theorem inf.le_left (x y : sys.Element) : sys.inf x y ≤ x :=
  Set.inter_subset_left

theorem inf.le_right (x y : sys.Element) : sys.inf x y ≤ y :=
  Set.inter_subset_right

end InfoSys
end DomainTheory.InformationSystems
