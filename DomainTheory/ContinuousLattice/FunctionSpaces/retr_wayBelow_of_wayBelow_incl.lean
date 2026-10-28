module
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_preservesDirectedSup
public import DomainTheory.ContinuousLattice.FunctionSpaces.IsContinuousLatticeRetraction
public import DomainTheory.ContinuousLattice.FunctionSpaces.monotone
public import DomainTheory.ContinuousLattice.ScottMaps.scottOpen_preimage
public import DomainTheory.ContinuousLattice.WayBelow.WayBelow
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Data.Set.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace

variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']

namespace IsContinuousLatticeRetraction

theorem retr_wayBelow_of_wayBelow_incl (R : IsContinuousLatticeRetraction D D')
    {d : D} {x' : D'} (hx' : x' ≪ R.incl d) : R.retr x' ≪ d := by
  obtain ⟨U', hU'open, hd_in, hU'sub⟩ := hx'
  refine ⟨(R.incl : D → D') ⁻¹' U', scottOpen_preimage R.incl_preservesDirectedSup hU'open,
    hd_in, fun z hz => ?_⟩
  have hle : x' ≤ R.incl z := Set.mem_Ici.1 (hU'sub hz)
  have hjle := R.retr.monotone hle
  rw [R.retr_incl z] at hjle
  exact Set.mem_Ici.2 hjle

end IsContinuousLatticeRetraction
end DomainTheory.ContinuousLattice
