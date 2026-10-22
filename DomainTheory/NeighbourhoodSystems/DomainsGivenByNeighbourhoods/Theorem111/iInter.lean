module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import Mathlib.Order.Monotone.Basic

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

/-- **Theorem 1.11 (i).** The intersection `⋂ₙ xₙ = {X ∣ ∀ n, X ∈ xₙ}` of a sequence of elements is
again an element of `|𝒟|`. (No proviso: all of 1.6(i)–(iii) are pointwise.) -/
def iInter (x : ℕ → V.Element) : V.Element where
  mem X := ∀ n, (x n).mem X
  sub h := (x 0).sub (h 0)
  master_mem n := (x n).master_mem
  inter_mem h1 h2 n := (x n).inter_mem (h1 n) (h2 n)
  up_mem h hY hXY n := (x n).up_mem (h n) hY hXY

end NeighborhoodSystem

end DomainTheory.NeighbourhoodSystems
