/-ai
Stage-n entailment of a raw lambda token by a finite set of raw tokens is the stratification of Scott's clauses (8) through (11). At stage zero, bottom is entailed exactly by stage-zero consistency, an atom is entailed when the set is stage-zero consistent, its atom set is nonempty, and the underlying information system entails that atom, and a function token is not entailed. At a successor stage the entailment already holds at the previous stage, or else bottom is entailed by successor consistency, an atom is entailed when the set is successor-consistent, its function set is empty, its atom set is nonempty, and the information system entails that atom, and a function token is entailed when the set is successor-consistent, its atom set is empty, both argument lists are consistent at the previous stage, and some subset of its function set has every input token entailed at the previous stage by the input list and every token of the output list entailed at the previous stage by the output union of that subset.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Sum
public import Mathlib.Data.Finset.Card
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.RawLamToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamEntDepth
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.LamConN
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst23
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid82.BasicInst27

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α : Type*} [DecidableEq α]

variable (A : InfoSys α)

/-- Stage-`n` entailment on raw tokens (Scott (8)–(11), stratified). -/
def LamEntN : ℕ → Finset (RawLamToken α) → RawLamToken α → Prop
  | 0, u, .bot => LamConN A 0 u
  | 0, u, .atom x =>
      LamConN A 0 u ∧ lamAtomFinset u ≠ ∅ ∧ A.Ent (lamAtomFinset u) x
  | 0, _, .funTok _ _ => False
  | n + 1, u, t =>
      LamEntN n u t ∨
        match t with
        | .bot => LamConN A (n + 1) u
        | .atom x =>
            LamConN A (n + 1) u ∧ lamFunFinset u = ∅ ∧
              lamAtomFinset u ≠ ∅ ∧ A.Ent (lamAtomFinset u) x
        | .funTok u' v' =>
            LamConN A (n + 1) u ∧ lamAtomFinset u = ∅ ∧
              LamConN A n (listToFinset u') ∧ LamConN A n (listToFinset v') ∧
              ∃ s ⊆ lamFunFinset u,
                (∀ p ∈ s, ∀ t ∈ listToFinset p.1, LamEntN n (listToFinset u') t) ∧
                  (∀ t ∈ listToFinset v', LamEntN n (lamOutputUnion s) t)

end InfoSys

end DomainTheory.InformationSystems
