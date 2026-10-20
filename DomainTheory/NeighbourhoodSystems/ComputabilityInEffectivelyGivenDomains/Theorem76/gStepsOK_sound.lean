module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.FixedPointsAndRecursion.Theorem41
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem76.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α : Type*} {V : NeighborhoodSystem α}




/-- **Soundness of a chain.** A valid `g`-chain from `a` realises the iterate relation
`(gᵏ).rel (X_a) (X_{last})` with `k` the chain length. -/
theorem gStepsOK_sound (g : ApproximableMap V V) (P : ComputablePresentation V) :
    ∀ (full : List ℕ) (a : ℕ), gStepsOK g P a full →
      (g.iterMap full.length).rel (P.X a) (P.X (gLastOf a full)) := by
  intro full
  induction full with
  | nil =>
    intro a _
    show (g.iterMap ([] : List ℕ).length).rel (P.X a) (P.X a)
    rw [List.length_nil, iterMap_zero]
    exact idMap_rel.mpr ⟨P.mem_X a, P.mem_X a, subset_rfl⟩
  | cons b rest ih =>
    intro a hsteps
    obtain ⟨h1, hrest⟩ := hsteps
    have hcomm : g.iterMap (rest.length + 1) = (g.iterMap rest.length).comp g := by
      rw [iterMap_succ]; exact iter_comm g rest.length
    show (g.iterMap (b :: rest).length).rel (P.X a) (P.X (gLastOf b rest))
    rw [List.length_cons, hcomm, comp_rel]
    exact ⟨P.X b, h1, ih b hrest⟩

end DomainTheory.NeighbourhoodSystems
