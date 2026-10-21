/-ai
Unfolding a lambda token into the carrier of the sum of A with its function space, following Scott's matching, sends bottom to the sum bottom and an atom to the left injection. A function token whose input and output lists are well formed is sent to the right injection of those two lists, each lifted to a finset of depth-well-formed tokens and shown consistent.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.IsLamWF_of_mem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.lambdaSystem
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.listToLamDFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon_listToLamDFinset

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Unfold a λ-token into the sum-of-function-space carrier (Scott’s matching). -/
def lamUnfold (t : LamDToken A) :
    SumToken α (FunToken (lambdaSystem A) (lambdaSystem A)) :=
  match t with
  | ⟨.bot, _⟩ => .bot
  | ⟨.atom x, _⟩ => .left x
  | ⟨.funTok xs ys, ⟨hxs, hys⟩⟩ =>
      let u := listToLamDFinset A xs fun _w hw =>
        IsLamWF_of_mem A hxs ((mem_listToFinset).2 hw)
      let v := listToLamDFinset A ys fun _w hw =>
        IsLamWF_of_mem A hys ((mem_listToFinset).2 hw)
      .right ⟨(u, v), ⟨LamDCon_listToLamDFinset A xs hxs,
        LamDCon_listToLamDFinset A ys hys⟩⟩

end InfoSys

end DomainTheory.InformationSystems
