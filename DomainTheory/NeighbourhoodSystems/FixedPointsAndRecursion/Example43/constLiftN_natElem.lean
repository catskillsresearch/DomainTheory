module

public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.natElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroElt
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.constLiftN
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.succMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.predMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroVal
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.zeroMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.memN_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.univ_ne_singleton
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_ne_univ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.singleton_nat_inj
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.nestedOrDisjoint
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_mem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.N_master
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example43.T
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
