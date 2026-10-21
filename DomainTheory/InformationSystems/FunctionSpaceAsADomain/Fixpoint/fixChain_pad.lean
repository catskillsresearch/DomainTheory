/-ai
A fix chain of length n for a consistent set w of function tokens remains a fix chain of length n + k for every k.

The argument is by induction on k. The zero case is the given chain, and the successor case is the one-step padding lemma.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_pad_front

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)

theorem fixChain_pad {w : Finset (FunToken A A)} {n k : Nat} {v : Finset α}
    (hw : FunCon A A w) (h : FixChain A w n v) : FixChain A w (n + k) v := by
  induction k with
  | zero => exact h
  | succ k ih => exact fixChain_pad_front A hw ih

end InfoSys

end DomainTheory.InformationSystems
