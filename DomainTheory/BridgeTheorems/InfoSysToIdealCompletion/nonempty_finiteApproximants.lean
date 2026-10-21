/-ai
The set of finite approximants of an element x is nonempty.

The bottom finite element belongs to it, because the bottom element lies under x and a finite element lying under x is a finite approximant of x.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Ideal
import all Mathlib.Order.Ideal
public import DomainTheory.InformationSystems.DomainsAsLatticesAndAsTopologicalSpaces.Factoid45
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.botFinite
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.finiteApproximants
public import DomainTheory.BridgeTheorems.InfoSysToIdealCompletion.mem_finiteApproximants_of_le

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open Order

namespace InfoSysToIdealCompletion

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem nonempty_finiteApproximants (x : A.Element) :
    (finiteApproximants A x).Nonempty :=
  ⟨botFinite A, mem_finiteApproximants_of_le A (A.botElement_le x)⟩

end InfoSysToIdealCompletion

end DomainTheory.BridgeTheorems
