/-ai
A raw lambda token is well formed for the information system when it is bottom or an atom, or when it is a function token whose two argument lists, read as finsets, are both depth-consistent. The earlier staged well-formedness predicate remains scaffolding.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
import all Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Well-formed tokens under depth Con (Scott (1)–(3) for the InfoSys instance).
Early staged `IsLamToken` / `LamToken` remain scaffolding only. -/
def IsLamWF : RawLamToken α → Prop
  | .bot | .atom _ => True
  | .funTok xs ys => LamConDepth A (listToFinset xs) ∧ LamConDepth A (listToFinset ys)

end InfoSys

end DomainTheory.InformationSystems
