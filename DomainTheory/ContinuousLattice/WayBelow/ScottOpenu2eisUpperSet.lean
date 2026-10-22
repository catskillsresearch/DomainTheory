module

public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen

@[expose] public section


namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]


theorem ScottOpen.isUpperSet {U : Set D} (h : ScottOpen U) : IsUpperSet U := h.1

end DomainTheory.ContinuousLattice
