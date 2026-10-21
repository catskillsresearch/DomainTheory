/-ai
This file gathers and re-exports the constructions of Scott's Factoid 7.5 on strict approximable maps, the strictify operator, the strict function space, flat BOOL, and the conditional isomorphism of a product with the strict maps out of BOOL, together with the tokens, satisfaction, consistency, entailment, elements, and supporting lemmas those constructions use.
ai-/

module

public import Mathlib.Data.Multiset.MapFold
import all Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Theorem72
public import DomainTheory.InformationSystems.InformationSystems.Factoid25
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid33
public import DomainTheory.InformationSystems.ElementsOfASystem.Factoid35

public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.EmptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictify
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrictToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.StrictFunEnt
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictFunctionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.approxMap_toStrictElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.strictifyElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolTrue
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolFalse
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.condElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_botElement_emptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.emptyEntails_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict_strictify
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat_bot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolSat_sing
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.mem_toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset_subset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset_insert
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.toFunFinset_singleton
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.insert_filter_ne_strict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.filter_ne_subset_of_subset_insert_strict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrictToken_of_IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_ent_empty_tru
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.not_ent_empty_fls
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.boolCon_trichotomy
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.subset_of_entSet_mem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.Factoid75.IsStrict_condMap

@[expose] public section

/-!
# Factoid 7.5 — strict mappings, `strictify`, BOOL, and the conditional

**Scott 1982 (after Prop 7.4).** Strict approximable maps; Scott’s `strict` /
`strictify` operator; InfoSys `A →ₛ B`; flat BOOL; `A × A ≅ (BOOL →ₛ A)`.
-/

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

set_option linter.unusedSectionVars false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]







variable (A : InfoSys α) (B : InfoSys β)

namespace ApproximableMap



end ApproximableMap

/-! ## BOOL -/





/-! ## Strict function space `A →ₛ B` -/















/-! ## Strict maps as elements; retract via `strictify` -/


open ApproximableMap



/-! ## Conditional: `A × A ≅ (BOOL →ₛ A)` -/









end InfoSys
end DomainTheory.InformationSystems
