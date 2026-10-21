/-ai
An element lies in a neighbourhood after the sum combinator if and only if either the which-map of the sum extraction meets zero and the left branch meets the neighbourhood, or the which-map meets one and the right branch meets the neighbourhood, or the neighbourhood is the master of the universal domain. The left branch is the sum injection after the left injection after the first map after the left extraction, and the right branch is the corresponding composite for the second map.

Rewrite by the composite form of the sum combinator, the elementwise laws of composition and of pairing, and the elementwise law of the conditional.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition89
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Definition83
public import DomainTheory.NeighbourhoodSystems.DomainEquations.Theorem69
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition810.sumComb_eq

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Exercise326


variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}


/-- **Elementwise unfolding of `sumComb`.** Chains `sumComb_eq`, `toElementMap_comp`, and
`toElementMap_paired`, landing exactly on `cond_toElementMap_mem`'s pattern. -/
theorem toElementMap_sumComb_mem (a b : ApproximableMap U U) (x : U.Element) {Z : Set ℚ} :
    ((sumComb a b).toElementMap x).mem Z ↔
      (((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap (jPlus.toElementMap x)).mem
          Example12.zero ∧
        (iPlus.toElementMap ((inMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (a.toElementMap ((outMap₀ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (jPlus.toElementMap x))))).mem Z) ∨
      (((whichMap U U U_mem_nonempty U_mem_nonempty).toElementMap (jPlus.toElementMap x)).mem
          Example12.one ∧
        (iPlus.toElementMap ((inMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
          (b.toElementMap ((outMap₁ (h₀ := U_mem_nonempty) (h₁ := U_mem_nonempty)).toElementMap
            (jPlus.toElementMap x))))).mem Z) ∨
      Z = U.master := by
  rw [sumComb_eq]
  simp only [toElementMap_comp, toElementMap_paired]
  rw [cond_toElementMap_mem]

end DomainTheory.NeighbourhoodSystems
