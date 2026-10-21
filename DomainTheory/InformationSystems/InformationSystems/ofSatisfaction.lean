/-ai
From a satisfaction relation, a least token satisfied by every point, and a point satisfying each single token, one builds an information system whose consistent sets are the finite sets satisfied at a common point and whose entailment requires such a common point together with semantic consequence. A subset of a commonly satisfied set is commonly satisfied by the same point. A singleton is consistent by the inhabitation hypothesis, after membership is rewritten to equality with the token. Inserting an entailed token keeps a common point, because semantic consequence covers the new token and the old point covers the remaining members. The least token is entailed because every point satisfies it, a member is entailed because any common point already satisfies it, and transitivity uses the common point of the intermediate set together with the semantic clause of each intermediate entailment.
ai-/
module

public import Mathlib.Algebra.Order.Field.Rat
import all Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Tactic.Linarith
import all Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
import all Mathlib.Tactic.NormNum
public import DomainTheory.InformationSystems.InformationSystems.InfoSys
public import DomainTheory.InformationSystems.InformationSystems.Factoid25.Token
public import DomainTheory.InformationSystems.InformationSystems.instDecidableEq
public import DomainTheory.InformationSystems.InformationSystems.Sat
public import DomainTheory.InformationSystems.InformationSystems.sat_sing

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

namespace Factoid25

/-- Generic information system from a satisfaction relation with a true `bot`
and inhabited singletons (Scott’s “obvious interpretation”).

`Ent` packages consistency of the left-hand set together with semantic entailment,
matching Scott’s typing of `⊢` as a relation on `Con × D` and making `ent_con`
hold (a purely vacuous `∀`-entailment from an inconsistent set would not). -/
def ofSatisfaction {τ : Type*} [DecidableEq τ] {Point : Type*}
    (Sat : Point → τ → Prop) (bot : τ)
    (sat_bot : ∀ p, Sat p bot)
    (sat_sing : ∀ t, ∃ p, Sat p t) : InfoSys τ where
  bot := bot
  Con := {u | ∃ p, ∀ t ∈ u, Sat p t}
  Ent u X := (∃ p, ∀ t ∈ u, Sat p t) ∧ ∀ p, (∀ t ∈ u, Sat p t) → Sat p X
  con_subset := by
    rintro u v ⟨p, hp⟩ hsub
    exact ⟨p, fun t ht => hp t (hsub ht)⟩
  con_sing := by
    intro a
    obtain ⟨p, hp⟩ := sat_sing a
    exact ⟨p, fun t ht => by
      rw [Finset.mem_singleton] at ht
      subst ht
      exact hp⟩
  ent_con := by
    rintro u a ⟨⟨p, hp⟩, hEnt⟩
    exact ⟨p, fun t ht => by
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact hEnt p hp
      · exact hp t ht'⟩
  ent_bot := by
    intro u hu
    exact ⟨hu, fun p _ => sat_bot p⟩
  ent_refl := by
    intro u a hu ha
    exact ⟨hu, fun p hp => hp a ha⟩
  ent_trans := by
    intro u v c hv _hu hvu ⟨_, huEnt⟩
    refine ⟨hv, fun p hp => huEnt p ?_⟩
    intro y hy
    exact (hvu y hy).2 p hp

end Factoid25

end DomainTheory.InformationSystems
