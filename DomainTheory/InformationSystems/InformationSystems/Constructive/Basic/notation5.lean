/-ai
This notation introduces the infix ∪' for the choice-free binary union of finite sets.
ai-/
module

public import Mathlib.Data.Finset.Basic
import all Mathlib.Data.Finset.Basic
public import DomainTheory.InformationSystems.InformationSystems.Constructive.funion

@[expose] public section

namespace DomainTheory.InformationSystems.Constructive

variable {α : Type*} [DecidableEq α]

@[inherit_doc] infixl:65 " ∪' " => funion

end DomainTheory.InformationSystems.Constructive
