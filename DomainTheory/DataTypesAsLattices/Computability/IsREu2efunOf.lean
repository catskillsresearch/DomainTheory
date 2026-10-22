module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Lambda
public import DomainTheory.DataTypesAsLattices.Computability.Basic
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2ecomp
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eand
public import DomainTheory.DataTypesAsLattices.Computability.REPredu2eexists
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2epair_mem
public import DomainTheory.DataTypesAsLattices.Computability.IsREu2eeSubset

@[expose] public section


set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices


open Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

/-- **Scott 1976, Appendix.** Application of r.e. elements is r.e. -/
theorem IsRE.funOf {u x : Pomega} (hu : IsRE u) (hx : IsRE x) : IsRE (u ⬝ x) := by
  have hand : REPred fun q : ℕ × ℕ => e q.1 ⊆ x ∧ pair q.1 q.2 ∈ u :=
    REPred.and ((IsRE.eSubset hx).comp Computable.fst) (IsRE.pair_mem hu)
  have hex : REPred fun m => ∃ n, e n ⊆ x ∧ pair n m ∈ u :=
    REPred.exists (p := fun m n => e n ⊆ x ∧ pair n m ∈ u)
      (hand.comp (Primrec.pair Primrec.snd Primrec.fst).to_comp)
  constructor
  exact hex.of_eq fun _ => Iff.rfl

end DomainTheory.DataTypesAsLattices
