
module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.Deg_isSubalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.Deg_self
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSubalgebra_isSubalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.GeneratedSubalgebra_generator
public import DomainTheory.DataTypesAsLattices.Enumeration.combinatory_mem_subalgebra
public import DomainTheory.DataTypesAsLattices.Enumeration.theorem_3_6_generated

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


/-- Exact finite-generation classification of enumeration degrees. -/
theorem theorem_3_6 (A : Set Pomega) :
    (∃ a, A = Deg a) ↔
      ∃ xs : List Pomega, A = GeneratedSubalgebra xs := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨[a], ?_⟩
    ext u
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact (GeneratedSubalgebra_isSubalgebra [a]).out.2
        (combinatory_mem_subalgebra (GeneratedSubalgebra_isSubalgebra [a]) hr)
        (GeneratedSubalgebra_generator (by simp))
    · intro hu
      exact hu _ (Deg_isSubalgebra a) (by
        intro x hx
        simp at hx
        subst x
        exact Deg_self a)
  · rintro ⟨xs, rfl⟩
    exact ⟨singleGenerator xs, theorem_3_6_generated xs⟩

end DomainTheory.DataTypesAsLattices
