/-ai
The value of p at the fin-code of j is contained in the Myhill operator of val and p applied to the finite set coded by j. This is the appendix inclusion of Theorem 3.5.

If m lies in that value, the index j is a finite piece of the finite set, and the pair of j and m lies in the operator after rewriting by the value of fin.
ai-/

module

public import Mathlib.Computability.Halting
import all Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.valNat_fin

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


/-- Appendix inclusion of Theorem 3.5: `val(p(fin j)) ⊆ q(e j)`. -/
theorem theorem_3_5_q_app (p : ℕ → ℕ) (j : ℕ) :
    valNat (p (fin j)) ⊆ funOf (myhillQ valNat p) (e j) := by
  intro m hm
  exact ⟨j, subset_rfl, ⟨j, m, rfl, by simpa [valNat_fin] using hm⟩⟩

end DomainTheory.DataTypesAsLattices
