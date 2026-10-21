/-ai
No right token belongs to the carrier of the bottom element of a separated sum.

Such a membership would be an entailment of the right token by the singleton of the sum bottom, and that entailment requires the right part of the singleton to be nonempty, whereas the right part of the singleton of the sum bottom is empty.
ai-/
module

public import Mathlib.Order.Hom.Basic
import all Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
import all Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
import all Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem not_right_mem_sum_botElement {y : β} :
    SumToken.right y ∉ ((sumSystem A B).botElement).carrier := by
  intro hy
  have hEnt : (sumSystem A B).Ent {sumBot} (.right y) := hy
  rcases hEnt with ⟨_, ⟨hne, _⟩⟩
  exact hne rhtFinset_singleton_bot

end InfoSysConstructions

end DomainTheory.BridgeTheorems
