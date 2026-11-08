module

public import DomainTheory.InformationSystems.InformationSystems.InfoSys.Element
public import DomainTheory.InformationSystems.ElementsOfASystem.IsTotal

@[expose] public section

namespace DomainTheory.InformationSystems

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)

def AllConsistent : Prop := ∀ u : Finset α, u ∈ sys.Con

def topElement (h : sys.AllConsistent) : sys.Element where
  carrier := Set.univ
  consistent := fun Y _ => h Y
  closed := fun _ _ _ _ => trivial

namespace topElement

theorem exists_top_iff_allConsistent :
    (∃ x : sys.Element, x.carrier = Set.univ) ↔ sys.AllConsistent := by
  constructor
  · intro ⟨x, hx⟩ u
    exact x.consistent u (hx ▸ Set.subset_univ _)
  · intro h
    exact ⟨sys.topElement h, rfl⟩

theorem le (h : sys.AllConsistent) (x : sys.Element) :
    x ≤ sys.topElement h := fun _ _ => trivial

theorem isTotal (h : sys.AllConsistent) :
    sys.IsTotal (sys.topElement h) := fun y _ => le sys h y

theorem eq_of_carrier_univ_of_isTotal {x t : sys.Element}
    (hx : x.carrier = Set.univ) (ht : sys.IsTotal t) : t = x :=
  le_antisymm (fun _ _ => hx ▸ trivial) (ht x (fun _ _ => hx ▸ trivial))

theorem isTotal_of_carrier_univ {x : sys.Element} (hx : x.carrier = Set.univ) :
    sys.IsTotal x := fun _ _ _ _ => hx ▸ trivial

theorem eq_of_isTotal (h : sys.AllConsistent) {x : sys.Element}
    (hx : sys.IsTotal x) : x = sys.topElement h :=
  le_antisymm (le sys h x) (hx _ (le sys h x))

theorem isTotal_iff_eq (h : sys.AllConsistent) {x : sys.Element} :
    sys.IsTotal x ↔ x = sys.topElement h :=
  ⟨eq_of_isTotal sys h, fun hx => hx ▸ isTotal sys h⟩

theorem exists_unique_total_of_allConsistent (h : sys.AllConsistent) :
    ∃! x : sys.Element, sys.IsTotal x :=
  ⟨sys.topElement h, ⟨isTotal sys h, fun _ hy => eq_of_isTotal sys h hy⟩⟩

end topElement

end InfoSys
end DomainTheory.InformationSystems
