/-ai
The elementwise image of the least fixed point of an approximable endomap is the least fixed point itself.

Extensionality of elements splits the equality. A neighbourhood of the image comes from an n-step chain and one further step, which together form a chain of length n + 1. A chain of length zero forces the neighbourhood to be the master, which belongs to the least fixed point and is related to itself by the map. A chain of successor length exposes an intermediate neighbourhood of the least fixed point and a last step, which is membership in the image.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.FunctionSpace
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.ApproximableExercises
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}

namespace ApproximableMap













/-- **Theorem 4.1 (Scott 1981, PRG-19).** `fixElement f` is a *fixed point*: `f(x) = x`.
`f(x) ⊆ x` appends an `f`-step (`Δ f^{n+1} X` from `Δ fⁿ X' f X`); `x ⊆ f(x)` reads off the last
step of the chain (the empty chain forces `X = Δ`, handled by `master_mem`/`master_rel`). -/
theorem toElementMap_fixElement (f : ApproximableMap V V) :
    f.toElementMap f.fixElement = f.fixElement := by
  apply Element.ext
  intro Y
  constructor
  · rintro ⟨X, ⟨n, hn⟩, hXY⟩
    exact ⟨n + 1, ⟨X, hn, hXY⟩⟩
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      obtain ⟨_, hYmem, hmY⟩ := hn
      have hYmaster : Y = V.master := Set.Subset.antisymm (V.sub_master hYmem) hmY
      subst hYmaster
      exact ⟨V.master, f.fixElement.master_mem, f.master_rel⟩
    | succ k =>
      obtain ⟨Z, hZ, hZY⟩ := hn
      exact ⟨Z, ⟨k, hZ⟩, hZY⟩

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
