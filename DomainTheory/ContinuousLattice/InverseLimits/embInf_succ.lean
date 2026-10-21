/-ai
The stage embeddings satisfy the recursion equation of Scott's section 4: embedding into the limit from stage n+1 after the stage inclusion equals embedding into the limit from stage n.

The underlying sequences are compared at an arbitrary coordinate m. When n and n+1 are both at most m, both components climb, and climbing after the first inclusion agrees with climbing from stage n. When n is at most m but n+1 is not, m equals n; the left side descends by one projection and the retraction-after-inclusion identity returns x, while the right side is x at its own stage. When n is not at most m, n+1 is not at most m either; both components descend, and peeling one projection is undone by the retraction-after-inclusion identity.
ai-/
module

public import DomainTheory.ContinuousLattice.Theorem212
public import Mathlib.Order.GaloisConnection.Basic
import all Mathlib.Order.GaloisConnection.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.Basic
public import DomainTheory.ContinuousLattice.InverseLimits.embLE_succ_left

@[expose] public section


namespace DomainTheory.ContinuousLattice

open Set

universe u

section InverseLimit

variable (D : ℕ → Type u) [∀ n, CompleteLattice (D n)]
variable (P : ∀ n, IsContinuousLatticeProjection (D n) (D (n + 1)))


/-- **Scott 1972, §4 (recursion equation).** `i_{n∞} = i_{(n+1)∞} ∘ iₙ`. -/
theorem embInf_succ (n : ℕ) (x : D n) :
    embInf D P (n + 1) ((P n).incl x) = embInf D P n x := by
  apply Subtype.ext
  funext m
  show iComp D P (n + 1) ((P n).incl x) m = iComp D P n x m
  by_cases h1 : n ≤ m
  · by_cases h2 : n + 1 ≤ m
    · rw [iComp_of_le D P h2, iComp_of_le D P h1, embLE_succ_left D P h1 h2]
    · have hmn : m = n := le_antisymm (Nat.lt_succ_iff.mp (not_le.mp h2)) h1
      subst hmn
      rw [iComp_self, iComp_of_ge D P h2,
        projLE_succ D P (le_refl m) (le_of_lt (not_le.mp h2)) ((P m).incl x),
        projLE_self, (P m).retr_incl]
  · have h2 : ¬ n + 1 ≤ m := fun h => h1 (le_trans (Nat.le_succ n) h)
    rw [iComp_of_ge D P h2, iComp_of_ge D P h1,
      projLE_succ D P (le_of_lt (not_le.mp h1)) (le_of_lt (not_le.mp h2)) ((P n).incl x),
      (P n).retr_incl]

end InverseLimit
end DomainTheory.ContinuousLattice
