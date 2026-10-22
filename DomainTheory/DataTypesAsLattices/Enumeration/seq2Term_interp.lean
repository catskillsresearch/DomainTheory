/-ai
If terms a and b both avoid the variable 8, then interpreting their term-level binary sequence constructor in an environment yields the binary sequence constructor of the two interpretations.

Unfolding the term and the constructor, the graphs agree. For each argument, the interpretations of a and of b are unchanged when the environment is updated at 8, because those terms avoid 8, and the bottom term interprets as bottom; the conditional and predecessor clauses then match.
ai-/

module

public import Mathlib.Computability.Halting
public import DomainTheory.DataTypesAsLattices.Computability
public import DomainTheory.DataTypesAsLattices.Functionality
public import DomainTheory.DataTypesAsLattices.Enumeration.Basic
public import DomainTheory.DataTypesAsLattices.Enumeration.enumBottomTerm_interp
public import DomainTheory.DataTypesAsLattices.Enumeration.interp_avoids

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code


theorem seq2Term_interp (a b : Term) (ρ : ℕ → Pomega)
    (ha : a.Avoids 8) (hb : b.Avoids 8) :
    interp (seq2Term a b) ρ = seq2 (interp a ρ) (interp b ρ) := by
  unfold seq2Term seq2
  apply congrArg graph
  funext z
  simp only [interp]
  rw [interp_avoids a ρ z ha, interp_avoids b ρ z hb, enumBottomTerm_interp]
  simp [envSet, Function.update]

end DomainTheory.DataTypesAsLattices
