/-ai
In the truth domain, the conditional sends bottom in the test coordinate to bottom.

Extensionality and the membership law for the conditional reduce the claim to neighbourhoods. A neighbourhood related by the conditional arises from the zero branch, the one branch, or the master neighbourhood. The first two contradict the separation of the zero and one tokens from the master neighbourhood of bottom, and the master neighbourhood belongs to bottom. Conversely, a neighbourhood of bottom is the master neighbourhood, which the conditional law accepts.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Example44
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise419.Basic

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise326.cond_toElementMap_mem
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise419

open DomainTheory.NeighbourhoodSystems NeighborhoodSystem ApproximableMap ExampleB Example44


variable {β : Type*}


/-- `cond(⊥, x, y) = ⊥` in `T`, phrased with `T.bot` (which the head-test `empty(⊥)` produces)
rather than the syntactically distinct `Example23.botElt` of `Exercise326.cond_bot`. -/
theorem condT_bot (x y : T.Element) :
    (Exercise326.cond T).toElementMap (pair T.bot (pair x y)) = T.bot := by
  apply Element.ext
  intro Z
  rw [Exercise326.cond_toElementMap_mem]
  constructor
  · rintro (⟨h0, _⟩ | ⟨h1, _⟩ | rfl)
    · rw [NeighborhoodSystem.mem_bot] at h0; exact absurd h0 Exercise326.zero_ne_master
    · rw [NeighborhoodSystem.mem_bot] at h1; exact absurd h1 Exercise326.one_ne_master
    · exact T.bot.master_mem
  · intro h
    rw [NeighborhoodSystem.mem_bot] at h
    exact Or.inr (Or.inr h)

end DomainTheory.NeighbourhoodSystems.Exercise419
