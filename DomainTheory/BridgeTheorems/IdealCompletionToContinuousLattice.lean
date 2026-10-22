module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Directed
public import DomainTheory.ContinuousLattice.WayBelow
public import DomainTheory.BridgeTheorems.IsCompactElement
public import DomainTheory.BridgeTheorems.AlgebraicLattice

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
open scoped DomainTheory.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]


/-- Compactness implies `Set.Ici k` is Scott-open. -/
theorem scottOpen_Ici_of_compact {k : D} (hk : IsCompactElement k) :
    ScottOpen (Set.Ici k) := by
  refine ⟨isUpperSet_Ici k, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s, hsS, hks⟩ := hk hS hSdir (Set.mem_Ici.1 hmem)
  exact ⟨s, hsS, Set.mem_Ici.2 hks⟩

/-- Compact elements are way below anything above them. -/
theorem compact_wayBelow {k y : D} (hk : IsCompactElement k) (hky : k ≤ y) : k ≪ y :=
  ⟨Set.Ici k, scottOpen_Ici_of_compact hk, Set.mem_Ici.2 hky, subset_rfl⟩


/-- **Blueprint:** algebraic complete lattice ⇒ continuous lattice (Scott Def. 2.3). -/
theorem isContinuousLattice_of_algebraic (hA : AlgebraicLattice D) :
    ContinuousLattice D := by
  constructor
  intro y
  obtain ⟨hne, hdir, hsup⟩ := hA.out y
  refine ⟨?_, fun z hz => ?_⟩
  · -- y is an upper bound of `{x | x ≪ y}`
    intro x hx
    exact hx.le
  · -- any upper bound of the way-belows is ≥ y
    -- every compact ≤ y is ≪ y, hence ≤ z
    have hle : sSup {x : D | IsCompactElement x ∧ x ≤ y} ≤ z := by
      refine sSup_le fun x hx => ?_
      exact hz (compact_wayBelow hx.1 hx.2)
    exact hsup ▸ hle

end IdealCompletionToContinuousLattice

/-- Blueprint name. -/
abbrev idealCompletion_to_continuousLattice {D : Type*} [CompleteLattice D]
    (hA : IdealCompletionToContinuousLattice.AlgebraicLattice D) :
    ContinuousLattice D :=
  IdealCompletionToContinuousLattice.isContinuousLattice_of_algebraic hA

end DomainTheory.BridgeTheorems
