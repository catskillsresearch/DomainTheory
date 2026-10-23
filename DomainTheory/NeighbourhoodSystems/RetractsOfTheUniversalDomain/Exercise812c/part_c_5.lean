module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.IntervalPrimrec
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem88
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Exercise812c.part_c_4
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition71.IsEffectivelyGiven
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.DAtomDecidable.DAtom_eq_empty_iff

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems
namespace testBit

open NeighborhoodSystem


/-- **The bitwise "and-not" identity**: `a ^^^ (a &&& b) = a` on bits where `b`'s bit is `0`, and
`= 0` on bits where `b`'s bit is `1` (whether or not `a`'s bit is set) — i.e. exactly "`a`'s bits
with `b`'s bits cleared". Mirrors `levelSet.inter`'s own `&&&`-formula; here `^^^` combines with
`&&&` instead, since `a &&& b` is always a "submask" of `a` (every set bit of `a &&& b` is already a
set bit of `a`), so XOR-ing it out just clears exactly those shared bits. -/
theorem xor_and_self (a b : ℕ) (i : ℕ) :
    (a ^^^ (a &&& b)).testBit i = (a.testBit i && !b.testBit i) := by
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

end testBit
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems
namespace levelSet

open NeighborhoodSystem


/-- **`levelSet` is closed under set-difference, unconditionally** — mirrors `levelSet.inter`
exactly, combining `upsample`-to-a-common-level with the "and-not" bit identity
`testBit.xor_and_self` in place of plain `&&&`. -/
theorem diff (k₁ m₁ k₂ m₂ : ℕ) :
    levelSet k₁ m₁ \ levelSet k₂ m₂
      = levelSet (max k₁ k₂)
          (let a := _root_.DomainTheory.NeighbourhoodSystems.upsample k₁ (max k₁ k₂) m₁
           let b := _root_.DomainTheory.NeighbourhoodSystems.upsample k₂ (max k₁ k₂) m₂
           a ^^^ (a &&& b)) := by
  rw [← levelSet.upsample (le_max_left k₁ k₂) (m := m₁),
    ← levelSet.upsample (le_max_right k₁ k₂) (m := m₂)]
  ext n
  simp only [mem_levelSet, Set.mem_sdiff, testBit.xor_and_self, Bool.and_eq_true, Bool.not_eq_true,
    Bool.not_eq_true']

end levelSet
end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


/-- **`V` is closed under set-difference of two of its own neighbourhoods** (or the difference is
empty). -/
theorem V_diff_mem {X Y : Set ℕ} (hX : V.mem X) (hY : V.mem Y) : X \ Y = ∅ ∨ V.mem (X \ Y) := by
  obtain ⟨k₁, m₁, rfl, -⟩ := hX
  obtain ⟨k₂, m₂, rfl, -⟩ := hY
  rcases Set.eq_empty_or_nonempty (levelSet k₁ m₁ \ levelSet k₂ m₂) with h | h
  · exact Or.inl h
  · exact Or.inr ⟨max k₁ k₂, _, levelSet.diff k₁ m₁ k₂ m₂, h⟩

end DomainTheory.NeighbourhoodSystems

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem


theorem V_diffClosed : V.DiffClosed := fun hX hY => V_diff_mem hX hY

end DomainTheory.NeighbourhoodSystems
