module

public import Mathlib.Order.Hom.Basic
public import Mathlib.Order.Sum.Order
public import Mathlib.Order.WithBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Proposition64
public import DomainTheory.BridgeTheorems.InfoSysConstructions.rhtFinset_singleton_left

@[expose] public section

namespace DomainTheory.BridgeTheorems

open DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

open DomainTheory.InformationSystems.InfoSys

open DomainTheory.InformationSystems.InfoSys.ApproximableMap

namespace InfoSysConstructions

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (A : InfoSys α) (B : InfoSys β)

theorem left_bot_mem_inlMap_toElement (x : A.Element) :
    SumToken.left A.bot ∈ ((inlMap A B).toElement x).carrier := by
  refine ⟨{A.bot}, ?_, ?_⟩
  · intro a ha
    have : a = A.bot := Finset.mem_singleton.mp (Finset.mem_coe.1 ha)
    subst this
    exact factoid_3_2 A x
  · refine ⟨A.con_sing A.bot, ?_, rhtFinset_singleton_left (β := β) A.bot, ?_⟩
    · exact Or.inl ⟨by rw [lftFinset_singleton_left]; exact A.con_sing A.bot,
        rhtFinset_singleton_left (β := β) A.bot⟩
    · rw [lftFinset_singleton_left]
      exact proposition_2_3_iii A (A.con_sing A.bot)

end InfoSysConstructions

end DomainTheory.BridgeTheorems
