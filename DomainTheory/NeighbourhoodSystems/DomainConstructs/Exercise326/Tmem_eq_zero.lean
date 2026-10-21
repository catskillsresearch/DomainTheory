/-ai
A neighbourhood of the truth domain contained in the singleton of zero equals that singleton.

Of the three neighbourhoods, the master contains one and the singleton of one contains one, neither of which lies in the singleton of zero, so the neighbourhood is the singleton of zero.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- A `T`-neighbourhood contained in `{0}` is `{0}` (the other two, `Δ` and `{1}`, are not). -/
theorem Tmem_eq_zero {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.zero) :
    C = Example12.zero := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 1)) (by simp [Example12.zero])
  · rfl
  · exact absurd (h (by simp [Example12.one] : (1 : Example12.Token) ∈ Example12.one))
      (by simp [Example12.zero])

end DomainTheory.NeighbourhoodSystems.Exercise326
