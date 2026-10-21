/-ai
If y is distinct from top, a finite set u entails y, and inserting y makes u entail top, then u already entails top.

Induct on y. When y is bottom and the inserted derivation is by membership of top, that top already belongs to u, since the inserted token is bottom. When the derivation uses both projections, inserting bottom leaves both projections unchanged, and the both-projections clause applies again. The case in which y is top contradicts the hypothesis that y is distinct from top. When y is a left pair and the derivation is by membership, top already belongs to u. When it uses both projections, rewriting shows that the left projection is the original left projection with the inner token inserted and the right projection is unchanged. Inverting the entailment of the left pair yields either membership of top in u, giving a top-entailment by membership, or an entailment of the inner token by the left projection of u. If the inner token is top, the both-projections clause applies to that left entailment of top and the unchanged right projection. Otherwise the inductive hypothesis turns the inserted left projection's top-entailment back into a top-entailment of the original left projection, and the both-projections clause combines it with the right projection. The right-pair case is symmetric, with the roles of the two projections exchanged.
ai-/
module

public import DomainTheory.InformationSystems.ProductsAndSumsOfDomains.Product
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VToken
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset_insert_bot
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairLFinset_insert_pairR
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.vPairRFinset_insert_pairL
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_pairL_inv
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.VEnt_pairR_inv
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst33
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst35
public import DomainTheory.InformationSystems.SomeDomainEquations.Factoid83.BasicInst39

@[expose] public section

set_option linter.unusedSectionVars false

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

/-- If inserting a non-top `y` creates a top-entailment and `u ⊢ y`, then already `u ⊢ ∇`. -/
theorem VEnt_insert_top_imp {u : Finset VToken} {y : VToken}
    (hy : y ≠ .top) (hEnt : VEnt u y) (hIns : VEnt (insert y u) .top) :
    VEnt u .top := by
  induction y generalizing u with
  | bot =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_bot] at hL
      rw [vPairRFinset_insert_bot] at hR
      exact VEnt.top_both hL hR
  | top => exact False.elim (hy rfl)
  | pairL x ih =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_pairL] at hL
      rw [vPairRFinset_insert_pairL] at hR
      rcases VEnt_pairL_inv hEnt with htop | hx
      · exact VEnt.top_mem htop
      · by_cases hxTop : x = .top
        · subst hxTop; exact VEnt.top_both hx hR
        · exact VEnt.top_both (ih hxTop hx hL) hR
  | pairR z ih =>
    cases hIns with
    | top_mem hm =>
      rcases Finset.mem_insert.mp hm with h | h
      · exact False.elim (nomatch h)
      · exact VEnt.top_mem h
    | top_both hL hR =>
      rw [vPairLFinset_insert_pairR] at hL
      rw [vPairRFinset_insert_pairR] at hR
      rcases VEnt_pairR_inv hEnt with htop | hz
      · exact VEnt.top_mem htop
      · by_cases hzTop : z = .top
        · subst hzTop; exact VEnt.top_both hL hz
        · exact VEnt.top_both hL (ih hzTop hz hR)

end InfoSys

end DomainTheory.InformationSystems
