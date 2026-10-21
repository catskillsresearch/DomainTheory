/-ai
A neighbourhood of the truth domain contained in the singleton of one equals that singleton.

Of the three neighbourhoods, the master contains zero and the singleton of zero contains zero, neither of which lies in the singleton of one, so the neighbourhood is the singleton of one.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Product
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Example23

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise326

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap

variable {α : Type*}

/-- A `T`-neighbourhood contained in `{1}` is `{1}`. -/
theorem Tmem_eq_one {C : Set Example12.Token} (hC : Example12.mem C) (h : C ⊆ Example12.one) :
    C = Example12.one := by
  rcases (Example12.mem_iff C).mp hC with rfl | rfl | rfl
  · exact absurd (h (Set.mem_univ 0)) (by simp [Example12.one])
  · exact absurd (h (by simp [Example12.zero] : (0 : Example12.Token) ∈ Example12.zero))
      (by simp [Example12.one])
  · rfl

end DomainTheory.NeighbourhoodSystems.Exercise326
