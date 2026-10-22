/-ai
The singleton of an atom is consistent.

Stage zero is a witness. The atom projection equals that singleton, which is consistent by the singleton axiom of A, and the function-token projection is empty because an atom is not a function token.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem LamCon_singleton_atom (x : α) :
    LamCon A ({.atom x} : Finset (RawLamToken α)) := by
  refine ⟨0, ?_⟩
  change lamAtomFinset _ ∈ A.Con ∧ lamFunFinset _ = ∅
  constructor
  · have h : lamAtomFinset ({.atom x} : Finset (RawLamToken α)) = {x} := by
      ext y
      simp only [mem_lamAtomFinset, Finset.mem_singleton]
      exact ⟨RawLamToken.atom.inj, congrArg RawLamToken.atom⟩
    rw [h]; exact A.con_sing x
  · ext p
    constructor
    · intro hp; exact False.elim (nomatch mem_lamFunFinset.1 hp)
    · intro hp; exact False.elim (Finset.notMem_empty p hp)

end InfoSys
end DomainTheory.InformationSystems
