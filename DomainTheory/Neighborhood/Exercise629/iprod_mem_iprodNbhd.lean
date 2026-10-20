/-
Copyright (c) 2026  Lars Warren Ericson.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars Warren Ericson.
Github:  https://github.com/catskillsresearch/DomainTheory
-/

import DomainTheory.Neighborhood.Product
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import DomainTheory.Neighborhood.Exercise629.Basic


namespace DomainTheory.Neighborhood

open NeighborhoodSystem

namespace Exercise629

universe u v

variable {ι : Type u} {α : ι → Type v}







variable {D : ∀ i, NeighborhoodSystem (α i)}




section IndexedProduct

variable [Nonempty ι]

variable (D) in

theorem iprod_mem_iprodNbhd {X : ∀ i, Set (α i)} (hX : ∀ i, (D i).mem (X i))
    (hXf : FinSupp D X) : (iprod D).mem (iprodNbhd X) :=
  ⟨X, hX, hXf, rfl⟩

end IndexedProduct
end Exercise629
end DomainTheory.Neighborhood
