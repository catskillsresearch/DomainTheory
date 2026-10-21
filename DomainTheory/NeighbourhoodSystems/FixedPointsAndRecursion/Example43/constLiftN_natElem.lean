/-ai
The strict lift sends the total element at n to the chosen value at n.

By extensionality of elements, a neighbourhood of the image is witnessed by an input belonging to that total element, hence the whole space or the singleton of n. The blunt clause yields the master of the chosen value. A singleton witness must be that same singleton, and then the output belongs to the value. Conversely, the singleton of n belongs to the total element and is related to any neighbourhood of the value.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.Basic
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.mem_natElem_iff

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Example43

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

















/-- **Computation on the total elements.** `f(n̂) = val n`. -/
theorem constLiftN_natElem {β : Type*} (V : NeighborhoodSystem β) (val : ℕ → V.Element) (n : ℕ) :
    (constLiftN V val).toElementMap (natElem n) = val n := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, hXmem, hrel⟩
    rw [mem_natElem_iff] at hXmem
    rcases hrel with ⟨_, rfl⟩ | ⟨k, hXk, hY⟩
    · exact (val n).master_mem
    · rcases hXmem with rfl | rfl
      · exact (univ_ne_singleton k hXk).elim
      · have hnk : n = k := singleton_nat_inj hXk
        subst hnk; exact hY
  · intro hY
    exact ⟨{n}, mem_natElem_iff.mpr (Or.inr rfl), Or.inr ⟨n, rfl, hY⟩⟩

end DomainTheory.NeighbourhoodSystems.Example43
