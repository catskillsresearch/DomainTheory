module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Example78
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem74
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Theorem75
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Exercise514
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.Basic
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise723.testBit_orUpTo

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems.Exercise723

open DomainTheory.NeighbourhoodSystems Example78 NeighborhoodSystem Domain.Recursive
open DomainTheory.NeighbourhoodSystems.Exercise513 (tri num numP unnum nextCell numP_unnum)
open DomainTheory.NeighbourhoodSystems.Exercise514 (tag tag_nil tag_cons Fun Fun_mono entries
  num_succ_left_gt tag_injective)
























/-- **`orUpTo n m n` computes the Minkowski sum `Eₙ + Eₘ` exactly.** Every set bit `a` of `n`
satisfies `a < n` (`lt_of_testBit_true`), so ranging `a` over `N = n` sees every set bit of `n`. -/
theorem testBit_orUpTo_self (n m k : ℕ) :
    (orUpTo n m n).testBit k = true ↔ ∃ a, a ≤ k ∧ n.testBit a = true ∧ m.testBit (k - a) = true := by
  rw [testBit_orUpTo]
  constructor
  · rintro ⟨a, _, ha, hak, hb⟩; exact ⟨a, hak, ha, hb⟩
  · rintro ⟨a, hak, ha, hb⟩; exact ⟨a, lt_of_testBit_true ha, ha, hak, hb⟩

end DomainTheory.NeighbourhoodSystems.Exercise723
