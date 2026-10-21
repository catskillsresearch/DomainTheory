/-ai
Every singleton of a depth-well-formed lambda token is bundled-consistent.

The forgetful image is the singleton of the underlying raw token. Matching on bottom, an atom, or a function token uses the corresponding raw singleton lemma, and the function-token case takes the two component consistencies from well-formedness.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_atom
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForgetFinset_singleton
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConDepth_singleton_funTok
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamDCon_singleton (p : LamDToken A) : LamDCon A {p} := by
  rw [LamDCon, lamDForgetFinset_singleton]
  match p.val, p.property with
  | .bot, _ => exact LamConDepth_singleton_bot A
  | .atom x, _ => exact LamConDepth_singleton_atom A x
  | .funTok xs ys, ⟨hxs, hys⟩ => exact LamConDepth_singleton_funTok A xs ys hxs hys

end InfoSys

end DomainTheory.InformationSystems
