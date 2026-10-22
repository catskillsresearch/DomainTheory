module

public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Pairing
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.Basic
public import Mathlib.Computability.Partrec
public import Mathlib.Tactic.Ring
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Regular
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Decide
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise722Equiv
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.Basic

@[expose] public section


namespace Domain.Recursive


open DomainTheory.NeighbourhoodSystems Exercise722
open DomainTheory.NeighbourhoodSystems.Exercise722


theorem primrec_codeBound : Nat.Primrec codeBound := by
  have hstep : Nat.Primrec (fun w => Nat.pair 1 w.unpair.2 + 1) :=
    primrec_add₂ (Nat.Primrec.pair (Nat.Primrec.const 1) Nat.Primrec.right)
      (Nat.Primrec.const 1)
  have haux : ∀ n, Nat.rec (motive := fun _ => ℕ) 1
      (fun y IH => Nat.pair 1 (Nat.pair y IH).unpair.2 + 1) n = codeBound n := by
    intro n
    induction n with
    | zero => simp [codeBound]
    | succ n ih =>
      simp only [unpair_pair_snd] at ih ⊢
      simp [codeBound, ih]
  exact (Nat.Primrec.prec1 1 hstep).of_eq haux

end Domain.Recursive
