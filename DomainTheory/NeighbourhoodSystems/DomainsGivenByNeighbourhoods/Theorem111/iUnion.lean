/-ai
The union of an ascending sequence of elements consists of the sets of tokens that belong to some term. Such a set is a neighbourhood of that term. The master belongs to the zeroth term. If one set belongs to the term at n and another to the term at m, monotonicity places both in the term at the maximum of n and m, and the intersection law at that term applies. Upward closure remains at the same term.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Monotone.Basic
import all Mathlib.Order.Monotone.Basic
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Theorem111.mem_iInter

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Theorem 1.11 (ii).** For an **ascending** sequence `x₀ ⊑ x₁ ⊑ ⋯`, the union
`⋃ₙ xₙ = {X ∣ ∃ n, X ∈ xₙ}` is again an element of `|𝒟|`. The proviso (`Monotone x`) is used only in
the intersection law: `X ∈ xₙ`, `Y ∈ xₘ` ⟹ both in `x_{max n m}`. -/
def iUnion (x : ℕ → V.Element) (hmono : Monotone x) : V.Element where
  mem X := ∃ n, (x n).mem X
  sub := by rintro X ⟨n, hn⟩; exact (x n).sub hn
  master_mem := ⟨0, (x 0).master_mem⟩
  inter_mem := by
    rintro X Y ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, (x (max n m)).inter_mem ?_ ?_⟩
    · exact hmono (le_max_left n m) X hn
    · exact hmono (le_max_right n m) Y hm
  up_mem := by
    rintro X Y ⟨n, hn⟩ hY hXY
    exact ⟨n, (x n).up_mem hn hY hXY⟩

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
