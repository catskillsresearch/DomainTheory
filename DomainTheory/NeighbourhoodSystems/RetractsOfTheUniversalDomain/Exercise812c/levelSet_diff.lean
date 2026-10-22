module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.testBit_xor_and_self

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`levelSet` is closed under set-difference, unconditionally** — mirrors `levelSet_inter`
exactly, combining `upsample`-to-a-common-level with the "and-not" bit identity
`testBit_xor_and_self` in place of plain `&&&`. -/
theorem levelSet_diff (k₁ m₁ k₂ m₂ : ℕ) :
    levelSet k₁ m₁ \ levelSet k₂ m₂
      = levelSet (max k₁ k₂)
          (let a := upsample k₁ (max k₁ k₂) m₁
           let b := upsample k₂ (max k₁ k₂) m₂
           a ^^^ (a &&& b)) := by
  rw [← levelSet_upsample (le_max_left k₁ k₂) (m := m₁),
    ← levelSet_upsample (le_max_right k₁ k₂) (m := m₂)]
  ext n
  simp only [mem_levelSet, Set.mem_sdiff, testBit_xor_and_self, Bool.and_eq_true, Bool.not_eq_true,
    Bool.not_eq_true']

end DomainTheory.NeighbourhoodSystems
