/-ai
The empty finset of raw lambda tokens is consistent.

Stage zero is a witness: both the atom projection and the function-token projection are empty, and the empty set is consistent in A.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]





































variable (A : InfoSys α)



theorem LamCon_empty : LamCon A (∅ : Finset (RawLamToken α)) :=
  ⟨0, by
    change lamAtomFinset ∅ ∈ A.Con ∧ lamFunFinset ∅ = ∅
    rw [lamAtomFinset_empty, lamFunFinset_empty]
    exact ⟨A.con_empty, rfl⟩⟩

end InfoSys
end DomainTheory.InformationSystems
