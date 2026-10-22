module

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem46
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.genOp
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise422.nats

public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Exercise414.lfpSet_subset
@[expose] public section

namespace DomainTheory.NeighbourhoodSystems.Exercise422

open DomainTheory.NeighbourhoodSystems DomainTheory.NeighbourhoodSystems.Exercise414

variable {M : Type*} (zero : M) (succ : M → M)

/-- **Induction by minimality.** Any subset `s ⊆ N*` containing `0` and closed under `⁺` contains
all of `N`. (This is the heart of axiom (iii): `s` is a pre-fixed point of `g`, hence dominates the
least fixed point `nats`.) -/
theorem nats_induction (s : Set M) (h0 : zero ∈ s) (hsucc : ∀ n ∈ s, succ n ∈ s) :
    nats zero succ ⊆ s := by
  apply lfpSet_subset (genOp zero succ)
  rintro x (rfl | ⟨n, hn, rfl⟩)
  · exact h0
  · exact hsucc n hn

end DomainTheory.NeighbourhoodSystems.Exercise422
