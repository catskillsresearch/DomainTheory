
module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.basicOpen
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.toScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.ofScottContinuous
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.mono
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid46.toElement_directedSup

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

theorem eq_of_basicOpen_eq (A : InfoSys α) {x y : A.Element}
    (h : ∀ u : Finset α, x ∈ A.basicOpen u ↔ y ∈ A.basicOpen u) : x = y := by
  refine le_antisymm ?_ ?_
  · intro a ha
    have : x ∈ A.basicOpen {a} := by
      intro b hb
      have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
      subst this
      exact ha
    exact ((h {a}).1 this) (Finset.mem_coe.2 (Finset.mem_singleton_self a))
  · intro a ha
    have : y ∈ A.basicOpen {a} := by
      intro b hb
      have : b = a := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
      subst this
      exact ha
    exact ((h {a}).2 this) (Finset.mem_coe.2 (Finset.mem_singleton_self a))

end InfoSys
end DomainTheory.InformationSystems
