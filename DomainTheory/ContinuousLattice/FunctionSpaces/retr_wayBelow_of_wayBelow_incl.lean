/-ai
If an ambient element x' is way below the inclusion of an element d of the retract, then the retraction of x' is way below d. The argument uses that the retraction inverts the inclusion and is monotone. This is the heart of Scott's proof of Proposition 2.10.

A Scott-open witness for the ambient way-below relation pulls back along the inclusion to a Scott-open set of the retract, because the inclusion preserves directed suprema, and d lies in that preimage. If z lies in the preimage, then x' lies below the inclusion of z, so monotonicity of the retraction and the inverse equation place the retraction of x' below z.
ai-/
module

public import DomainTheory.ContinuousLattice.ScottMaps
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.Order
public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.FixedPoints
public import DomainTheory.ContinuousLattice.FunctionSpaces.Basic
public import DomainTheory.ContinuousLattice.FunctionSpaces.incl_preservesDirectedSup

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set Topology TopologicalSpace


variable {X Y D D' D'' D₀ D₀' D₁ D₁' : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y]
variable [CompleteLattice D] [CompleteLattice D'] [CompleteLattice D'']
variable [CompleteLattice D₀] [CompleteLattice D₀'] [CompleteLattice D₁] [CompleteLattice D₁']


namespace IsContinuousLatticeRetraction


/-- **Heart of Scott's proof of 2.10.** If `x' ≪ i(d)` in the ambient continuous lattice `D'`,
then its image `j(x')` is way below `d` in the retract `D`. The Scott-open witness in `D` is the
preimage `i⁻¹V'` of an ambient Scott-open witness `V'` (Scott-open because `i` preserves directed
suprema); for `z ∈ i⁻¹V'` we have `x' ⊑ i(z)`, hence `j(x') ⊑ j(i(z)) = z`. No projection
hypothesis is needed — `j ∘ i = id` and monotonicity suffice. -/
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
