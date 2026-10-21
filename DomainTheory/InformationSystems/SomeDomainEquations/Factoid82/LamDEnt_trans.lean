/-ai
If u and v are bundled-consistent, every token of u is bundled-entailed by v, and c is bundled-entailed by u, then c is bundled-entailed by v.

Depth-entailment transitivity applies. Each forgotten member of u is the underlying token of some member of u, and that member is entailed by v.
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
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth_trans
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst70
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst74
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.mem_lamDForgetFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDCon
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamDEnt

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

theorem LamDEnt_trans {u v : Finset (LamDToken A)} {c : LamDToken A}
    (hv : LamDCon A v) (hu : LamDCon A u)
    (hEnts : ∀ t ∈ u, LamDEnt A v t) (ht : LamDEnt A u c) :
    LamDEnt A v c :=
  LamEntDepth_trans A hv hu
    (fun t ht' => by
      rcases (mem_lamDForgetFinset A).1 ht' with ⟨p, hp, rfl⟩
      exact hEnts p hp)
    ht

end InfoSys

end DomainTheory.InformationSystems
