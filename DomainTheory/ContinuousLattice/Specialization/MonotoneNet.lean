module

public import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Directed
import Mathlib.Order.Monotone.Basic

@[expose] public section

namespace DomainTheory.ContinuousLattice

universe u

variable {D : Type u} [CompleteLattice D]

variable {ι : Type u} [Preorder ι] [IsDirected ι (· ≤ ·)]

class MonotoneNet (x : ι → D) : Prop where
  out : Monotone x

end DomainTheory.ContinuousLattice
