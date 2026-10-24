module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterElem
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixMap
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_zero
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.comp_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iterMap_mono_map
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.iter_comm
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.rel_master_succ
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.rel_master_mono
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.mem_fixElement
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.fixElement_mono

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap


/-- **Theorem 4.1 (Scott 1981, PRG-19).** `fixElement f` is the *least pre-fixed point*: if
`f(z) ⊆ z`, then `x ⊆ z`. (Scott's induction: `Δ ∈ z`, and `X ∈ z`, `X f Y` give `Y ∈ f(z) ⊆ z`,
so `Δ fⁿ X` implies `X ∈ z`.) In particular `x` is the least element with `f(x) = x`. -/
theorem fixElement_le_of_toElementMap_le (f : ApproximableMap V V) {z : V.Element}
    (hz : f.toElementMap z ≤ z) : f.fixElement ≤ z := by
  have key : ∀ n X, (f.iterMap n).rel V.master X → z.mem X := by
    intro n
    induction n with
    | zero =>
      intro X hn
      obtain ⟨_, hXmem, hmX⟩ := hn
      have hXmaster : X = V.master := Set.Subset.antisymm (V.sub_master hXmem) hmX
      subst hXmaster
      exact z.master_mem
    | succ k ih =>
      intro X hn
      obtain ⟨W, hW, hWX⟩ := hn
      exact hz X ⟨W, ih W hW, hWX⟩
  rintro X ⟨n, hn⟩
  exact key n X hn

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
