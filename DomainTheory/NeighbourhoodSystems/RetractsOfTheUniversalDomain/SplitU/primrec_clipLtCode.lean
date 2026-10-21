/-ai
clipLtCode is primitive recursive.

The midpoint and the two endpoints are primitive recursive projections. Pairing the left endpoint with the minimum of the right endpoint and the midpoint agrees with the clip by simplification.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem primrec_clipLtCode : Nat.Primrec clipLtCode := by
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have he1 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  exact (Nat.Primrec.pair he1 (primrec_ratMinCode.comp (he2.pair hm))).of_eq
    fun t => by simp only [clipLtCode]

end DomainTheory.NeighbourhoodSystems
