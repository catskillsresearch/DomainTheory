/-ai
If w' entails w in the function-space system and both sets are consistent, then every set reachable by a w-chain is reachable by a w'-chain.

A witnessing chain of some length transfers to w' by monotonicity of fix chains in the token set.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_mono_w

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixReach_mono_w {w w' : Finset (FunToken A A)} {v : Finset α}
    (hw : FunCon A A w) (hw' : FunCon A A w') (h : FixReach A w v)
    (hEntw : (functionSystem A A).EntSet w' w) : FixReach A w' v := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fixChain_mono_w A hw hw' hn hEntw⟩

end InfoSys

end DomainTheory.InformationSystems
