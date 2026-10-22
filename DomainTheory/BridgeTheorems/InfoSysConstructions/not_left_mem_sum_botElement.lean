/-ai
No left token belongs to the carrier of the bottom element of a separated sum.

Such a membership would be an entailment of the left token by the singleton of the sum bottom, and that entailment requires the left part of the singleton to be nonempty, whereas the left part of the singleton of the sum bottom is empty.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
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

theorem not_left_mem_sum_botElement {x : α} :
    SumToken.left x ∉ ((sumSystem A B).botElement).carrier := by
  intro hx
  have hEnt : (sumSystem A B).Ent {sumBot} (.left x) := hx
  -- Ent {bot} (left x) requires lftFinset {bot} ≠ ∅
  rcases hEnt with ⟨_, ⟨hne, _⟩⟩
  exact hne lftFinset_singleton_bot

end InfoSysConstructions

end DomainTheory.BridgeTheorems
