module

public import DomainTheory.ContinuousLattice.Theorem212.IdemFix
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

namespace IdemFix

variable {e : L → L}

@[reducible] noncomputable def supSet (hidem : ∀ x, e (e x) = e x) : SupSet (IdemFix e) :=
  ⟨fun S => ⟨e (sSup (Subtype.val '' S)), hidem _⟩⟩

end IdemFix

end FixedPoints

end DomainTheory.ContinuousLattice
