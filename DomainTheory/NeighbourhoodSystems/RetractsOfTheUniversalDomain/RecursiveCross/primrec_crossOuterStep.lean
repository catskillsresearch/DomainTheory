/-ai
If bop is primitive recursive, then crossOuterStep bop is primitive recursive.

The head, the accumulator, and the fixed list are primitive recursive projections. The inner cross of the head with the fixed list is primitive recursive by composing the inner-cross recursion with that pairing and simplifying the unpair-pair identities. Appending that result to the accumulator is primitive recursive by composing append-code recursion with the pairing, and unfolding the outer step reduces to the same identities.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.primrec_appendCode
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.primrec_crossInner

@[expose] public section


namespace Domain.Recursive


theorem primrec_crossOuterStep {bop : ℕ → ℕ} (hbop : Nat.Primrec bop) :
    Nat.Primrec (crossOuterStep bop) := by
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hc2 : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hinner : Nat.Primrec (fun w : ℕ => crossInner bop w.unpair.1 w.unpair.2.unpair.2) :=
    ((primrec_crossInner hbop).comp (hx.pair hc2)).of_eq fun w => by
      simp only [unpair_pair_fst, unpair_pair_snd]
  exact (primrec_appendCode.comp (hinner.pair hacc)).of_eq fun w => by
    unfold crossOuterStep
    simp only [unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive
