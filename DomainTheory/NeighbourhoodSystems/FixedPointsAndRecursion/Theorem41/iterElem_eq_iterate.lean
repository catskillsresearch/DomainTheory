/-ai
The n-th approximant equals the n-fold iterate of the elementwise map, applied to the bottom element.

The proof is induction on n. At zero the iterate is the identity map, and the elementwise action of the identity is the identity. At a successor the approximant is the elementwise image of the previous approximant, by the elementwise action of composition, and the inductive hypothesis replaces that approximant by the iterated function. The successor iterate of a function is one further application.
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


/-- `fⁿ(⊥)` agrees with the iterated elementwise function `(f(·))^[n] ⊥` — Scott's `fⁿ(⊥)`. -/
theorem iterElem_eq_iterate (f : ApproximableMap V V) (n : ℕ) :
    f.iterElem n = (f.toElementMap)^[n] V.bot := by
  induction n with
  | zero =>
    show (f.iterMap 0).toElementMap V.bot = V.bot
    exact toElementMap_idMap V.bot
  | succ k ih =>
    have hstep : f.iterElem (k + 1) = f.toElementMap (f.iterElem k) := by
      show (f.comp (f.iterMap k)).toElementMap V.bot
          = f.toElementMap ((f.iterMap k).toElementMap V.bot)
      rw [toElementMap_comp]
    rw [hstep, ih, Function.iterate_succ', Function.comp_apply]

end ApproximableMap
end DomainTheory.NeighbourhoodSystems
