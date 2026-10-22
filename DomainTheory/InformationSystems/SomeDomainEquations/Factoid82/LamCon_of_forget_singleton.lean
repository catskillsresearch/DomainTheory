/-ai
Forgetting a single well-formed lambda token yields a consistent finset of raw tokens.

The forgetful image of a singleton is the singleton of the underlying raw token. Matching on bottom, an atom, or a function token uses the corresponding singleton consistency, and the function-token case takes the two component consistencies from well-formedness.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.Basic
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamCon_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamCon_singleton_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamForgetFinset_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamCon_singleton_funTok

@[expose] public section


namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]


variable (A : InfoSys α)


theorem LamCon_of_forget_singleton (p : LamToken A) :
    LamCon A (lamForgetFinset A {p}) := by
  rw [lamForgetFinset_singleton]
  match p with
  | ⟨.bot, _⟩ => exact LamCon_singleton_bot A
  | ⟨.atom x, _⟩ => exact LamCon_singleton_atom A x
  | ⟨.funTok u v, hWF⟩ => exact LamCon_singleton_funTok A u v hWF.1 hWF.2

end InfoSys
end DomainTheory.InformationSystems
