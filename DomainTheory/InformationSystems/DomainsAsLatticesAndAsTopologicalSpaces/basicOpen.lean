module

public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Approximable
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.ScottContinuous

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def basicOpen (A : InfoSys α) (u : Finset α) : Set A.Element :=
  {x | ↑u ⊆ x.carrier}

namespace basicOpen

theorem inter (A : InfoSys α) (u v : Finset α) :
    A.basicOpen u ∩ A.basicOpen v = A.basicOpen (u ∪' v) := by
  ext x
  constructor
  · intro ⟨hu, hv⟩ a ha
    rcases funion.mem.mp (Finset.mem_coe.1 ha) with h | h
    · exact hu (Finset.mem_coe.2 h)
    · exact hv (Finset.mem_coe.2 h)
  · intro huv
    refine ⟨?_, ?_⟩
    · intro a ha
      exact huv (Finset.mem_coe.2 (funion.mem.mpr (Or.inl (Finset.mem_coe.1 ha))))
    · intro a ha
      exact huv (Finset.mem_coe.2 (funion.mem.mpr (Or.inr (Finset.mem_coe.1 ha))))

theorem mem {A : InfoSys α} {u : Finset α} {x : A.Element} :
    x ∈ A.basicOpen u ↔ ↑u ⊆ x.carrier := Iff.rfl

theorem eq_of_eq (A : InfoSys α) {x y : A.Element}
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

end basicOpen

end InfoSys
end DomainTheory.InformationSystems
