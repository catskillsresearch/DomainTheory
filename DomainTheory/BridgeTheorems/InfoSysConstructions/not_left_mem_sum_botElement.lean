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

set_option linter.unusedSectionVars false

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
