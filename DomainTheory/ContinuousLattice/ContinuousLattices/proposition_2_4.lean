module

public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

theorem proposition_2_4 :
    ContinuousLattice D ↔
      ∀ y : D, IsLUB {a : D | ∃ U, ScottOpen U ∧ y ∈ U ∧ a = sInf U} y :=
  isContinuousLattice_iff_isLUB_sInf_nhds

end DomainTheory.ContinuousLattice
