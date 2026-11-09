module

public import DomainTheory.InformationSystems.ElementsOfASystem.botElement

@[expose] public section

namespace DomainTheory.InformationSystems
namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def inf (x y : sys.Element) : sys.Element where
  carrier := x.carrier ∩ y.carrier
  consistent := fun Y hY =>
    x.consistent Y (Set.Subset.trans hY Set.inter_subset_left)
  closed := fun Y a hY hEnt =>
    ⟨x.closed Y a (Set.Subset.trans hY Set.inter_subset_left) hEnt,
     y.closed Y a (Set.Subset.trans hY Set.inter_subset_right) hEnt⟩

namespace inf

theorem le_left (x y : sys.Element) : sys.inf x y ≤ x :=
  Set.inter_subset_left

theorem le_right (x y : sys.Element) : sys.inf x y ≤ y :=
  Set.inter_subset_right

theorem le_inf {x y z : sys.Element} (hxy : x ≤ y) (hxz : x ≤ z) : x ≤ sys.inf y z :=
  fun _ ha => ⟨hxy ha, hxz ha⟩

theorem le_iff_eq {x y : sys.Element} : x ≤ y ↔ sys.inf x y = x := by
  constructor
  · intro h
    refine le_antisymm (le_left sys x y) ?_
    intro a ha
    exact ⟨ha, h ha⟩
  · intro heq
    have hc : x.carrier = x.carrier ∩ y.carrier :=
      Eq.symm (congrArg Element.carrier heq)
    intro a ha
    exact ((Set.ext_iff.1 hc a).1 ha).2

theorem le_iff {x y z : sys.Element} : z ≤ sys.inf x y ↔ z ≤ x ∧ z ≤ y :=
  ⟨fun h => ⟨le_trans h (le_left sys x y), le_trans h (le_right sys x y)⟩,
   fun ⟨hx, hy⟩ => le_inf sys hx hy⟩

theorem comm (x y : sys.Element) : sys.inf x y = sys.inf y x := by
  refine le_antisymm ?_ ?_
  · exact le_inf sys (le_right sys x y) (le_left sys x y)
  · exact le_inf sys (le_right sys y x) (le_left sys y x)

theorem assoc (x y z : sys.Element) : sys.inf (sys.inf x y) z = sys.inf x (sys.inf y z) := by
  refine le_antisymm ?_ ?_
  · refine le_inf sys ?_ (le_inf sys ?_ ?_)
    · exact le_trans (le_left sys _ _) (le_left sys _ _)
    · exact le_trans (le_left sys _ _) (le_right sys _ _)
    · exact le_right sys _ _
  · refine le_inf sys (le_inf sys ?_ ?_) ?_
    · exact le_left sys _ _
    · exact le_trans (le_right sys _ _) (le_left sys _ _)
    · exact le_trans (le_right sys _ _) (le_right sys _ _)

theorem idem (x : sys.Element) : sys.inf x x = x :=
  (le_iff_eq sys (y := x)).1 (le_refl x)

theorem mono {x₁ x₂ y₁ y₂ : sys.Element} (hx : x₁ ≤ x₂) (hy : y₁ ≤ y₂) :
    sys.inf x₁ y₁ ≤ sys.inf x₂ y₂ :=
  le_inf sys (le_trans (le_left sys _ _) hx) (le_trans (le_right sys _ _) hy)

theorem botElement_inf (x : sys.Element) : sys.inf sys.botElement x = sys.botElement :=
  (le_iff_eq sys (x := sys.botElement) (y := x)).1 (botElement.le sys x)

theorem inf_botElement (x : sys.Element) : sys.inf x sys.botElement = sys.botElement := by
  rw [comm sys, botElement_inf sys]

end inf

end InfoSys
end DomainTheory.InformationSystems
