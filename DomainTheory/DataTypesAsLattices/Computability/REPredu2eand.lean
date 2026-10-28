module

public import Mathlib.Computability.RE
public import DomainTheory.DataTypesAsLattices.Retracts.comp

@[expose] public section

set_option maxHeartbeats 2000000

namespace DomainTheory.DataTypesAsLattices

theorem REPred.and {α} [Primcodable α] {p q : α → Prop}
    (hp : REPred p) (hq : REPred q) :
    REPred fun a => p a ∧ q a := by
  refine (hp.bind (hq.comp Computable.fst).to₂).of_eq fun a => ?_
  ext
  simp [Part.assert]

end DomainTheory.DataTypesAsLattices
