/-ai
The right copy of the bottom token of B belongs to the carrier of the right image of every element of B.

The witness is the singleton of that bottom token. Its only token is the bottom token, which belongs to every element. The singleton is consistent in the sum by the right clause, because its right part is the consistent singleton of the bottom token and its left part is empty, and the entailment of the right bottom token is the entailment, in B, of that consistent singleton.
ai-/
module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.lftFinset_singleton_right

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem right_bot_mem_inrMap_toElement (y : B.Element) :
    SumToken.right B.bot ∈ ((inrMap A B).toElement y).carrier := by
  refine ⟨{B.bot}, ?_, ?_⟩
  · intro b hb
    have : b = B.bot := Finset.mem_singleton.mp (Finset.mem_coe.1 hb)
    subst this
    exact factoid_3_2 B y
  · refine ⟨B.con_sing B.bot, ?_, lftFinset_singleton_right (α := α) B.bot, ?_⟩
    · exact Or.inr ⟨lftFinset_singleton_right (α := α) B.bot,
        by rw [rhtFinset_singleton_right]; exact B.con_sing B.bot⟩
    · rw [rhtFinset_singleton_right]
      exact proposition_2_3_iii B (B.con_sing B.bot)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
