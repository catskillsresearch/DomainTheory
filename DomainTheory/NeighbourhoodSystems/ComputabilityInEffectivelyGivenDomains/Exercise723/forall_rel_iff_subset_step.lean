module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)


/-- **Membership in a function-space step set, as inclusion of `Xenum`s.** `∀ f ∈ W, f.rel X Y` iff
`W ⊆ step X Y` (`mem_step`); specialised to `W = Xenum … c` and the singleton step neighbourhood
(`Xenum_singleton`), this becomes the *decidable* function-space inclusion `incl_computable`. -/
theorem forall_rel_iff_subset_step {W : Set (ApproximableMap PN PN)} {n m₀ : ℕ} :
    (∀ f ∈ W, f.rel (nbhd n) (nbhd m₀)) ↔ W ⊆ step (nbhd n) (nbhd m₀) := by
  constructor
  · intro h f hf; exact mem_step.mpr (h f hf)
  · intro h f hf; exact mem_step.mp (h hf)

end DomainTheory.NeighbourhoodSystems.Exercise723
