/-ai
If bop is primitive recursive, then crossInnerStep bop is primitive recursive.

The head, the accumulator, and the fixed parameter are primitive recursive projections. Successor after pairing bop of the fixed parameter with the head together with the accumulator agrees with the inner step by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic

@[expose] public section


namespace Domain.Recursive


theorem primrec_crossInnerStep {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (crossInnerStep bop) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.succ.comp ((hbop.comp (hx.pair hy)).pair hacc)).of_eq fun _ => rfl

end Domain.Recursive
