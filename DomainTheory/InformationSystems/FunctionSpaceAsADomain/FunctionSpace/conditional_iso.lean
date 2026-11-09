module

public import Mathlib.Data.Multiset.MapFold
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.functionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.theorem_7_2
public import DomainTheory.InformationSystems.InformationSystems.a_second_example
public import DomainTheory.InformationSystems.ElementsOfASystem.botElement
public import DomainTheory.InformationSystems.ElementsOfASystem.closure
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BoolToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BoolPoint
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.EmptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.strictify
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.boolSat
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.boolSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.StrictToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.StrictFunToken
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.toFunFinset
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.StrictFunCon
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.StrictFunEnt
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.strictBot
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.strictFunctionSystem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.approxMap_toStrictElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.strictifyElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.boolTrue
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.boolFalse
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.condMap
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.condElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.emptyEntails_empty
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.emptyEntails_mem_botElement
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.mem_botElement_emptyEntails
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.emptyEntails_funion
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.BasicInst22
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.insert_filter_ne_strict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.filter_ne_subset_of_subset_insert_strict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.IsStrictToken_of_IsStrict
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.not_ent_empty_tru
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.not_ent_empty_fls
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.boolCon_trichotomy
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.subset_of_entSet_mem
public import DomainTheory.InformationSystems.FunctionSpaceAsADomain.FunctionSpace.condMap_unique

@[expose] public section

namespace DomainTheory.InformationSystems

open DomainTheory.InformationSystems.Constructive

namespace InfoSys

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

variable (A : InfoSys α) (B : InfoSys β)

open ApproximableMap

theorem conditional_iso (x y : A.Element) :
    (condMap A x y).toElement boolTrue = x ∧
    (condMap A x y).toElement boolFalse = y ∧
    ∀ (f : ApproximableMap boolSystem A), IsStrict boolSystem A f →
      f = condMap A (f.toElement boolTrue) (f.toElement boolFalse) :=
  ⟨condMap.toElement_boolTrue A x y, condMap.toElement_boolFalse A x y,
    fun f hf => condMap.unique A f hf⟩

end InfoSys
end DomainTheory.InformationSystems
