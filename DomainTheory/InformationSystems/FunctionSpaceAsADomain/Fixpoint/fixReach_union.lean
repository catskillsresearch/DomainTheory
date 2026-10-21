/-ai
The union of two sets reachable by w-chains, for a consistent set w of function tokens, is again reachable.

Pad the two chains to a common length by adding the other length, using commutativity of addition for the second chain, and then take the union of the padded chains.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_pad
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_union

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixReach_union {w : Finset (FunToken A A)} {v v' : Finset α}
    (hw : FunCon A A w) (h : FixReach A w v) (h' : FixReach A w v') :
    FixReach A w (v ∪' v') := by
  obtain ⟨n, hn⟩ := h
  obtain ⟨m, hm⟩ := h'
  have hn' : FixChain A w (n + m) v := fixChain_pad A hw hn
  have hm' : FixChain A w (m + n) v' := fixChain_pad A hw hm
  have hm'' : FixChain A w (n + m) v' := by rwa [Nat.add_comm] at hm'
  exact ⟨n + m, fixChain_union A hw hn' hm''⟩

end InfoSys

end DomainTheory.InformationSystems
