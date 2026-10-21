/-ai
A finite set reachable by a fix chain is consistent.

Reachability supplies a chain of some length, and every value of a fix chain is consistent.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_con

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixReach_con {w : Finset (FunToken A A)} {v : Finset α}
    (h : FixReach A w v) : v ∈ A.Con := by
  obtain ⟨_, hn⟩ := h
  exact fixChain_con A hn

end InfoSys

end DomainTheory.InformationSystems
