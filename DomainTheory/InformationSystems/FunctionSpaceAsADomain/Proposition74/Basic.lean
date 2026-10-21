/-ai
The closure of the empty consistent set of an information system is the bottom element. This is the empty-closure fact used for Scott's Proposition 7.4.

Antisymmetry is used. A token entailed by the empty set is entailed by the singleton of the bottom token, because the empty set is entailed by that singleton. A token entailed by the singleton of the bottom token is entailed by the empty set, because the unique member of that singleton is the bottom token and the bottom token is entailed by the empty consistent set.
ai-/
module

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Fixpoint
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition54
public import DomainTheory.InformationSystems.ApproximableMappingsBetweenDomains.Proposition55
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

@[expose] public section

/-!
# Proposition 7.4 — Plotkin’s equational characterization of `fix`

**Scott 1982, Proposition 7.4.** The least fixed-point operator is uniquely
determined by:
(i) `fix_A : (A → A) → A` for every system `A`;
(ii) `fix(f) = f(fix(f))`;
(iii) `h(fix_A(f)) = fix_B(g)` whenever `h ∘ f = g ∘ h` and `h(⊥_A) = ⊥_B`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys
namespace ApproximableMap

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (A : InfoSys α) (B : InfoSys β)

theorem closure_empty_eq_bot :
    A.closure (∅ : Finset α) A.con_empty = A.botElement := by
  apply le_antisymm
  · intro a ha
    exact A.ent_trans (A.con_sing A.bot) A.con_empty (A.entSet_empty _) ha
  · intro a ha
    exact A.ent_trans A.con_empty (A.con_sing A.bot)
      (fun x hx => by
        have : x = A.bot := Finset.mem_singleton.mp hx
        subst this
        exact A.ent_bot A.con_empty)
      ha
end ApproximableMap
end InfoSys
end DomainTheory.InformationSystems
