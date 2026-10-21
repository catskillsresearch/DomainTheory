/-ai
The function sending a packed pair to clipLtListCode of its two components is primitive recursive.

The map sending a pair code to the singleton list code of its downward clip is primitive recursive, as successor of that clip paired with zero. The flat map of that function agrees with the unpaired list clip by reflexivity.
ai-/
module

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.UComputablePresentation
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.Basic
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.SplitU.primrec_clipLtCode

@[expose] public section


namespace DomainTheory.NeighbourhoodSystems

open Domain.Recursive NeighborhoodSystem


theorem primrec_clipLtListCode : Nat.Primrec (fun t : ℕ => clipLtListCode t.unpair.1 t.unpair.2) := by
  have hg : Nat.Primrec (fun t : ℕ => Nat.pair (clipLtCode t) 0 + 1) :=
    Nat.Primrec.succ.comp (primrec_clipLtCode.pair (Nat.Primrec.const 0))
  exact (primrec_flatMapCode hg).of_eq fun _ => rfl

end DomainTheory.NeighbourhoodSystems
