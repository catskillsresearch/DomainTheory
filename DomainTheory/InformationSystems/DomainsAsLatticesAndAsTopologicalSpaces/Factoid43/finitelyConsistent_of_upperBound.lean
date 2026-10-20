module

public import DomainTheory.InformationSystems.InformationSystems.Constructive
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid42
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid43.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (sys : InfoSys α)






/-- An upper bound of `S` forces the carrier-union to be finitely consistent. -/
theorem finitelyConsistent_of_upperBound (S : Set sys.Element) {z : sys.Element}
    (h : ∀ x ∈ S, x ≤ z) : sys.IsFinitelyConsistent (sys.familyUnionCarrier S) := by
  intro Y hY
  have hYZ : (Y : Set α) ⊆ z.carrier := by
    intro a ha
    obtain ⟨x, hx, ha'⟩ := hY ha
    exact h x hx ha'
  exact z.consistent Y hYZ

end InfoSys
end DomainTheory.InformationSystems
