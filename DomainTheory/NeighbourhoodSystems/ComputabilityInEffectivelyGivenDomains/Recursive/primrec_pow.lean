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
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Recursive.recPow_eq

@[expose] public section


namespace Domain.Recursive


/-- **Exponentiation is primitive recursive** (`unpaired (b, e) ↦ b ^ e`), choice-free. -/
theorem primrec_pow : Nat.Primrec (Nat.unpaired fun b e => b ^ e) := by
  have hg : Nat.Primrec (fun w => w.unpair.2.unpair.2 * w.unpair.1) :=
    primrec_mul₂ (Nat.Primrec.right.comp Nat.Primrec.right) Nat.Primrec.left
  refine (Nat.Primrec.prec (Nat.Primrec.const 1) hg).of_eq (fun p => ?_)
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd]
  exact recPow_eq p.unpair.1 p.unpair.2

end Domain.Recursive
