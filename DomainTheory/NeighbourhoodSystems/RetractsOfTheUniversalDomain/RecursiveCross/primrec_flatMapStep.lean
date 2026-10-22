module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.RecursiveCross.primrec_appendCode

@[expose] public section


namespace Domain.Recursive


theorem primrec_flatMapStep {f : ℕ → ℕ} (hf : Nat.Primrec f) : Nat.Primrec (flatMapStep f) := by
  have hy : Nat.Primrec (fun w : ℕ => w.unpair.1) := Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (primrec_appendCode.comp ((hf.comp (hx.pair hy)).pair hacc)).of_eq fun w => by
    unfold flatMapStep; simp only [unpair_pair_fst, unpair_pair_snd]

end Domain.Recursive
