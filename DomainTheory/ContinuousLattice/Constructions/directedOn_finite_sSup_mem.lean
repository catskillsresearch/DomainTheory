module

public import DomainTheory.ContinuousLattice.MilnerCorrection
public import DomainTheory.ContinuousLattice.ScottMaps
public import DomainTheory.ContinuousLattice.Injective
public import Mathlib.Order.Preorder.Finite
import all Mathlib.Order.Preorder.Finite
public import DomainTheory.ContinuousLattice.Constructions.Basic

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Topology Set

variable {D : Type*} [CompleteLattice D]

/-- A non-empty **finite** directed set attains its supremum: `⊔S ∈ S`. A maximal element of
`S` (which exists by finiteness) is, by directedness, the greatest element, hence the
supremum. This is the order-theoretic heart of "finite ⟹ continuous" (Scott 1972, 2.8). -/
theorem directedOn_finite_sSup_mem {S : Set D} (hSfin : S.Finite) (hSne : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) : sSup S ∈ S := by
  obtain ⟨m, hm⟩ := hSfin.exists_maximal hSne
  have hub : m ∈ upperBounds S := by
    intro s hs
    obtain ⟨c, hcS, hmc, hsc⟩ := hSdir m hm.1 s hs
    exact hsc.trans (hm.2 hcS hmc)
  have hlub : IsLUB S m := ⟨hub, fun b hb => hb hm.1⟩
  rw [hlub.sSup_eq]
  exact hm.1

end DomainTheory.ContinuousLattice
