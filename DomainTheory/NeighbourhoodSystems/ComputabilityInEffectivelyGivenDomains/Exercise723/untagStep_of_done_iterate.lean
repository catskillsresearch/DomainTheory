/-ai
Once the done flag is one, every iterate of the untagging transition fixes the state.

The proof is induction on the number of iterations. Zero iterations are reflexive. A successor iterate rewrites by the inductive hypothesis and the one-step equation for a done state.
ai-/

module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.untagStep_done

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)






























































theorem untagStep_of_done_iterate (w : ℕ) (h : w.unpair.2.unpair.1 = 1) :
    ∀ k, untagStep^[k] w = w
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply', untagStep_of_done_iterate w h k, untagStep_done h]

end DomainTheory.NeighbourhoodSystems.Exercise723
