/-ai
Two elements of the neighbourhood system R that contain the same intervals [0, r) are equal.

Apply element extensionality. If a set belongs to the first element, the subproperty writes it as some [0, r), and the hypothesis transfers that membership to the second element. The converse is the same argument with the two elements exchanged.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem85
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Order.Bounds.OrderIso
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_mem_iff
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.R_master
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise811.a_rel

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise811

open NeighborhoodSystem ApproximableMap

/-- `R`'s elements are entirely determined by their membership at the endpoints `[0,r)`: two
elements agreeing on every `r` agree everywhere (any other `X` with `x.mem X` is forced, by
`x.sub`, to already be some `[0,r)`). -/
theorem Element.ext_U {x y : R.Element} (h : ∀ r : ℚ, x.mem (Set.Ico 0 r) ↔ y.mem (Set.Ico 0 r)) :
    x = y := by
  apply NeighborhoodSystem.Element.ext
  intro X
  constructor
  · intro hx
    obtain ⟨r, _, _, rfl⟩ := x.sub hx
    exact (h r).mp hx
  · intro hy
    obtain ⟨r, _, _, rfl⟩ := y.sub hy
    exact (h r).mpr hy

end DomainTheory.NeighbourhoodSystems.Exercise811
