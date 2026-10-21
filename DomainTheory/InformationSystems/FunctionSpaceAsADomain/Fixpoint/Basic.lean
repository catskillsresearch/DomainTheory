/-ai
A function token that belongs to a finite set contained in the element corresponding to an approximable endomap f lies in the relation of f.

Membership of a function token in that element is the relation of f, so the subset hypothesis gives the relation.
ai-/

module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixChain
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.FixReach
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_con
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_con
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_pad_front
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_pad
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.funEnt_union_step
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_union
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_union
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixChain_mono_w
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint.fixReach_mono_w

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72.mem_approxMap_toElement
@[expose] public section

/-!
# Least fixed-point operator — Theorem 7.3

**Scott 1982, Theorem 7.3.** Unique approximable `fix : (A → A) → A` such that
for every approximable `f : A → A`:
(ii) `f(fix(f)) ⊆ fix(f)` (in fact equality);
(iii) if `f(x) ⊆ x` then `fix(f) ⊆ x`.

`w (fix) v` means some `w`-chain from `∅` reaches a set that entails `v`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α] (A : InfoSys α)


namespace ApproximableMap


/-- Tokens of `w ⊆ approxMap_toElement f` satisfy `f.rel`. -/
theorem rel_of_mem_approx (f : ApproximableMap A A)
    {w : Finset (FunToken A A)}
    (hw : ↑w ⊆ (approxMap_toElement A A f).carrier) {p : FunToken A A}
    (hp : p ∈ w) : f.rel p.val.1 p.val.2 := by
  simpa [mem_approxMap_toElement] using hw (Finset.mem_coe.2 hp)
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
