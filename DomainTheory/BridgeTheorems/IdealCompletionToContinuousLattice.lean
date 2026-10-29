module

public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import DomainTheory.ContinuousLattice.WayBelow.ContinuousLattice
public import DomainTheory.BridgeTheorems.AlgebraicLattice
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Directed
public import Mathlib.Order.UpperLower.Basic
public import DomainTheory.ContinuousLattice.WayBelow.ScottOpen

public import DomainTheory.BridgeTheorems.IsCompactElement

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.ContinuousLattice
open scoped DomainTheory.ContinuousLattice

namespace IdealCompletionToContinuousLattice

variable {D : Type*} [CompleteLattice D]

theorem scottOpen_Ici_of_compact {k : D} (hk : IsCompactElement k) :
    ScottOpen (Set.Ici k) := by
  refine ⟨isUpperSet_Ici k, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s, hsS, hks⟩ := hk hS hSdir (Set.mem_Ici.1 hmem)
  exact ⟨s, hsS, Set.mem_Ici.2 hks⟩

theorem compact_wayBelow {k y : D} (hk : IsCompactElement k) (hky : k ≤ y) : k ≪ y :=
  ⟨Set.Ici k, scottOpen_Ici_of_compact hk, Set.mem_Ici.2 hky, subset_rfl⟩

theorem isContinuousLattice_of_algebraic (hA : AlgebraicLattice D) :
    ContinuousLattice D := by
  refine { out := ?_ }
  intro y
  obtain ⟨hne, hdir, hsup⟩ := hA.out y
  refine ⟨?_, fun z hz => ?_⟩
  ·
    intro x hx
    exact hx.le
  ·

    have hle : sSup {x : D | IsCompactElement x ∧ x ≤ y} ≤ z := by
      refine sSup_le fun x hx => ?_
      exact hz (compact_wayBelow hx.1 hx.2)
    exact hsup ▸ hle

end IdealCompletionToContinuousLattice

abbrev idealCompletion_to_continuousLattice {D : Type*} [CompleteLattice D]
    (hA : IdealCompletionToContinuousLattice.AlgebraicLattice D) :
    ContinuousLattice D :=
  IdealCompletionToContinuousLattice.isContinuousLattice_of_algebraic hA

end DomainTheory.BridgeTheorems
