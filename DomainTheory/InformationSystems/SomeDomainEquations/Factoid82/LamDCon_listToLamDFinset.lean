/-ai
A list of raw tokens whose finset is depth-consistent determines a bundled-consistent finset of depth-well-formed tokens, with well-formedness of each entry taken from membership in that finset.

Rewriting bundled consistency along the forgetful image of the packaged list returns the original finset, which is depth-consistent by hypothesis.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.IsLamWF_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lamDForget_listToLamDFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamDCon_listToLamDFinset (xs : List (RawLamToken α))
    (hCon : LamConDepth A (listToFinset xs)) :
    LamDCon A (listToLamDFinset A xs fun _t ht =>
      IsLamWF_of_mem A hCon ((mem_listToFinset).2 ht)) := by
  rw [LamDCon, lamDForget_listToLamDFinset]
  exact hCon

end InfoSys

end DomainTheory.InformationSystems
