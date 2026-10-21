/-ai
For a monotone idempotent endomap, the ambient-then-endomap supremum is a least upper bound in the fixed-point set.

A fixed point k of the set lies below the candidate because its underlying element equals the endomap applied to itself, and monotonicity carries that element up to the endomap applied to the ambient supremum of the underlying set. If w is an upper bound, each underlying member of the set lies below the underlying element of w, so the ambient supremum does too. Monotonicity of the endomap and the fixed-point equation for w put the candidate below w.
ai-/
module

public import DomainTheory.ContinuousLattice.Constructions
public import DomainTheory.ContinuousLattice.FunctionSpaces
public import DomainTheory.ContinuousLattice.Theorem212.IdemFix
public import DomainTheory.ContinuousLattice.Theorem212.supSet

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.ContinuousLattice

open Topology Set

section FixedPoints

variable {L : Type*} [CompleteLattice L]

namespace IdemFix

variable {e : L → L}

/-- With the ambient-then-`e` supremum, every set has a least upper bound in `IdemFix e`. This
needs only that `e` is monotone (which follows from Scott continuity). -/
theorem isLUB_sSup (hidem : ∀ x, e (e x) = e x) (hmono : Monotone e) :
    letI := supSet hidem
    ∀ S : Set (IdemFix e), IsLUB S (sSup S) := by
  let := supSet hidem
  intro S
  constructor
  · intro k hk
    rw [Subtype.coe_le_coe.symm, Subtype.coe_mk]
    show (k : L) ≤ e (sSup (Subtype.val '' S))
    calc (k : L) = e k := k.2.symm
      _ ≤ e (sSup (Subtype.val '' S)) :=
          hmono (le_sSup (Set.mem_image_of_mem _ hk))
  · intro w hw
    rw [Subtype.coe_le_coe.symm, Subtype.coe_mk]
    show e (sSup (Subtype.val '' S)) ≤ (w : L)
    calc e (sSup (Subtype.val '' S)) ≤ e (w : L) := by
          refine hmono (sSup_le ?_)
          rintro _ ⟨k, hk, rfl⟩
          exact hw hk
      _ = (w : L) := w.2

end IdemFix

end FixedPoints

end DomainTheory.ContinuousLattice
