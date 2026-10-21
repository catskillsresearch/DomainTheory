/-ai
Projecting the union of a coherent inverse-limit sequence by a Kleene stage recovers the coordinate at that stage.

Rewrite the projection of the union by the chain lemma for the continuous stage projection and the successive inclusions of the coordinates. An index in the projection of some coordinate falls into the desired coordinate by the earlier-projection equation and the chain when that coordinate is earlier, and by the later-projection equation when it is later. Conversely, an index of the desired coordinate lies in the corresponding summand by the later-projection equation at equal indices.
ai-/
module

public import DomainTheory.DataTypesAsLattices.FixedLattices
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Retracts.IsRetract
public import DomainTheory.DataTypesAsLattices.Retracts.retractLe
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst36
public import DomainTheory.DataTypesAsLattices.Retracts.IsStrict
public import DomainTheory.DataTypesAsLattices.Retracts.RetractInverseLimit
public import DomainTheory.DataTypesAsLattices.Retracts.BasicInst55
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_mono
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_chain
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_later
public import DomainTheory.DataTypesAsLattices.Retracts.inverseLimit_project_earlier

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.DataTypesAsLattices

/-- Every stage projection of the union of a coherent sequence is its
corresponding coordinate. -/
theorem inverseLimit_project_iUnion {F : Pomega → Pomega}
    (hf : IsScottContinuous F)
    (hret : ∀ a, IsRetract a → IsRetract (F a))
    (hstrict : ∀ a, IsRetract a → IsStrict a → IsStrict (F a))
    (hmono : ∀ {a b}, IsRetract a → IsStrict a →
      IsRetract b → IsStrict b → retractLe a b → retractLe (F a) (F b))
    (v : RetractInverseLimit F) (n : ℕ) :
    funOf (iterateBot F n) (⋃ m, v.1 m) = v.1 n := by
  rw [chain_lemma (funOf_isScottContinuous (iterateBot F n)) v.1
    (inverseLimit_mono hf v)]
  apply subset_antisymm
  · intro k hk
    obtain ⟨m, hkm⟩ := Set.mem_iUnion.mp hk
    by_cases hmn : m ≤ n
    · rw [inverseLimit_project_earlier hret hstrict hmono v hmn] at hkm
      exact inverseLimit_chain hf v m n hmn hkm
    · have hnm : n ≤ m := Nat.le_of_lt (Nat.lt_of_not_ge hmn)
      rwa [inverseLimit_project_later hret hstrict hmono v hnm] at hkm
  · intro k hk
    exact Set.mem_iUnion.mpr ⟨n, by
      rw [inverseLimit_project_later hret hstrict hmono v (le_refl n)]
      exact hk⟩

end DomainTheory.DataTypesAsLattices
