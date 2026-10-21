/-ai
The element determined by the ideal of finite approximants of an element x is x itself.

The carrier of that ideal equals the set of finite approximants of x. A member of the carrier is the underlying element of a finite approximant, and a finite approximant is the closure of a consistent finite set, hence is itself a finite element witnessing membership in the carrier. The directed supremum of this set is the directed supremum of the finite approximants of x, which is x.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.toIdeal
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.idealCarrier
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.ofIdeal

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem ofIdeal_toIdeal (x : A.Element) : ofIdeal A (toIdeal A x) = x := by
  -- idealCarrier (toIdeal x) = finiteApproximants as Elements = A.finiteApproximants x
  have hset : idealCarrier A (toIdeal A x) = A.finiteApproximants x := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := hz
      exact hy
    · intro hz
      refine ⟨⟨z, ?_⟩, hz, rfl⟩
      obtain ⟨u, hu, _, rfl⟩ := hz
      exact ⟨u, hu, rfl⟩
  -- directedSup of that set is x
  change A.directedSup (idealCarrier A (toIdeal A x)) _ _ = x
  simp_rw [hset]
  exact (A.eq_directedSup_finiteApproximants x).symm

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
