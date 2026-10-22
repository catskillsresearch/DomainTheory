module

public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Basic
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise315
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.ComputablePresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.inclShuffle
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.swapPair
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.reindexInvolutive
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.unitPresentation
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.inclShuffle
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.swapPair

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem Domain.Recursive

variable {α : Type*}


namespace ComputablePresentation

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)


theorem primrec_inclShuffle : Nat.Primrec inclShuffle :=
  Nat.Primrec.pair Nat.Primrec.left (Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left)


private theorem primrec_swapPair : Nat.Primrec swapPair :=
  Nat.Primrec.pair Nat.Primrec.right Nat.Primrec.left

/-- **Scott's biconditional after 7.1.** "The inclusion relation between neighbourhoods is itself
decidable in terms of the indices", because `Xₙ ⊆ Xₘ ↔ Xₙ ∩ Xₘ = Xₙ`. We obtain the decision by
reindexing `(n, m) ↦ (n, m, n)` into relation (i). -/
theorem incl_computable : RecDecidable₂ (fun n m => P.X n ⊆ P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_) (P.interEq_computable.comp primrec_inclShuffle)
  simp only [inclShuffle, unpair_pair_fst, unpair_pair_snd]
  exact Set.inter_eq_left.symm

/-- **Equality of neighbourhoods is decidable** from the indices: `Xₙ = Xₘ ↔ Xₙ ⊆ Xₘ ∧ Xₘ ⊆ Xₙ`,
so equality is the conjunction of `incl_computable` with its swap. -/
theorem eq_computable : RecDecidable₂ (fun n m => P.X n = P.X m) := by
  refine RecDecidable.of_iff (fun t => ?_)
    (P.incl_computable.and (P.incl_computable.comp primrec_swapPair))
  simp only [swapPair, unpair_pair_fst, unpair_pair_snd]
  exact Set.Subset.antisymm_iff


end ComputablePresentation


end DomainTheory.NeighbourhoodSystems
